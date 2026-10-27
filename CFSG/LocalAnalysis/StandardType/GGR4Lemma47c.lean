module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem r4l_inv_mul_mem_centralizer {G : Type} [Group G] {X : Subgroup G} {b k : G}
    (h : ∀ l ∈ X, b * l * b⁻¹ = k * l * k⁻¹) :
    k⁻¹ * b ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  calc l * (k⁻¹ * b) = k⁻¹ * (k * l * k⁻¹ * b) := by group
    _ = k⁻¹ * (b * l) := by rw [← h l hl]; group
    _ = k⁻¹ * b * l := by group

private theorem r4l_pow_mem_centralizer {G : Type} [Group G] {p : ℕ} {X : Subgroup G}
    {b k : G} (hk : k ∈ X) (h : ∀ l ∈ X, b * l * b⁻¹ = k * l * k⁻¹)
    (hb : b ^ p = 1) : k ^ p ∈ Subgroup.centralizer (X : Set G) := by
  have hc : k⁻¹ * b ∈ Subgroup.centralizer (X : Set G) :=
    r4l_inv_mul_mem_centralizer h
  have hkc : Commute k (k⁻¹ * b) := Subgroup.mem_centralizer_iff.mp hc k hk
  have hb_eq : b = k * (k⁻¹ * b) := by group
  have hbp : b ^ p = k ^ p * (k⁻¹ * b) ^ p := by
    conv_lhs => rw [hb_eq]
    exact hkc.mul_pow p
  have h1 : k ^ p * (k⁻¹ * b) ^ p = 1 := by rw [← hbp, hb]
  have hkpow : k ^ p = ((k⁻¹ * b) ^ p)⁻¹ := by
    calc k ^ p = k ^ p * (k⁻¹ * b) ^ p * ((k⁻¹ * b) ^ p)⁻¹ := by group
      _ = 1 * ((k⁻¹ * b) ^ p)⁻¹ := by rw [h1]
      _ = ((k⁻¹ * b) ^ p)⁻¹ := by group
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  rw [hkpow]
  exact Subgroup.mem_centralizer_iff.mp
    (Subgroup.inv_mem _ (Subgroup.pow_mem _ hc p)) l hl

private theorem r4l_exists_k0 {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hZ : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g))
    (hInn : ∀ b ∈ Bs, ∃ k ∈ X, ∀ l ∈ X, b * l * b⁻¹ = k * l * k⁻¹)
    {b : G} (hb : b ∈ Bs) :
    ∃ k0 ∈ X, k0 ^ p = 1 ∧ ∀ l ∈ X, b * l * b⁻¹ = k0 * l * k0⁻¹ := by
  obtain ⟨k, hkX, hkind⟩ := hInn b hb
  have hbp : b ^ p = 1 := hBs.2 b hb
  have hkzC : k ^ p ∈ Subgroup.centralizer (X : Set G) :=
    r4l_pow_mem_centralizer hkX hkind hbp
  have hkz_center : (⟨k ^ p, X.pow_mem hkX p⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hkzC l l.2
  have hcop : Nat.Coprime p (orderOf (⟨k ^ p, X.pow_mem hkX p⟩ : ↥X)) :=
    hZ _ hkz_center
  obtain ⟨m, hm1, hm0⟩ := Nat.chineseRemainder hcop 1 0
  have hodvd : orderOf (⟨k ^ p, X.pow_mem hkX p⟩ : ↥X) ∣ m :=
    Nat.modEq_zero_iff_dvd.mp hm0
  refine ⟨k ^ m, X.pow_mem hkX m, ?_, ?_⟩
  · have hsub : (⟨k ^ p, X.pow_mem hkX p⟩ : ↥X) ^ m = 1 :=
      (orderOf_dvd_iff_pow_eq_one).mp hodvd
    have hG : (k ^ p) ^ m = 1 := by
      have h' := congrArg Subtype.val hsub
      simpa [Subgroup.coe_pow] using h'
    calc (k ^ m) ^ p = (k ^ p) ^ m := by
          rw [← pow_mul, Nat.mul_comm m p, pow_mul]
      _ = 1 := hG
  · have hmpos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · exfalso
        subst h0
        have hp2 : 1 < p := (Fact.out : p.Prime).one_lt
        have hmod : (0 : ℕ) % p = 1 % p := hm1
        rw [Nat.zero_mod, Nat.mod_eq_of_lt hp2] at hmod
        omega
      · exact hpos
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hmpos).mp hm1.symm
    have hm_eq : m = 1 + p * t := by omega
    have hkm : k ^ m = k * (k ^ p) ^ t := by
      rw [hm_eq, pow_add, pow_mul, pow_one]
    have hkptC : (k ^ p) ^ t ∈ Subgroup.centralizer (X : Set G) :=
      Subgroup.pow_mem _ hkzC t
    intro l hl
    have hptl : (k ^ p) ^ t * l * ((k ^ p) ^ t)⁻¹ = l := by
      calc (k ^ p) ^ t * l * ((k ^ p) ^ t)⁻¹
          = l * (k ^ p) ^ t * ((k ^ p) ^ t)⁻¹ := by
              rw [(Subgroup.mem_centralizer_iff.mp hkptC l hl).symm]
        _ = l := by group
    calc b * l * b⁻¹ = k * l * k⁻¹ := hkind l hl
      _ = k * ((k ^ p) ^ t * l * ((k ^ p) ^ t)⁻¹) * k⁻¹ := by rw [hptl]
      _ = k ^ m * l * (k ^ m)⁻¹ := by rw [hkm]; group

private theorem r4l_actions_comm {G : Type} [Group G] {X : Subgroup G} {b b' k0 k1 : G}
    (hk0X : k0 ∈ X) (hk1X : k1 ∈ X)
    (hk0ind : ∀ l ∈ X, b * l * b⁻¹ = k0 * l * k0⁻¹)
    (hk1ind : ∀ l ∈ X, b' * l * b'⁻¹ = k1 * l * k1⁻¹)
    (hbb' : b * b' = b' * b) :
    ∀ m ∈ X, k0 * (k1 * m * k1⁻¹) * k0⁻¹ = k1 * (k0 * m * k0⁻¹) * k1⁻¹ := by
  intro m hm
  have hm1 : k1 * m * k1⁻¹ ∈ X := X.mul_mem (X.mul_mem hk1X hm) (X.inv_mem hk1X)
  have hm0 : k0 * m * k0⁻¹ ∈ X := X.mul_mem (X.mul_mem hk0X hm) (X.inv_mem hk0X)
  calc k0 * (k1 * m * k1⁻¹) * k0⁻¹
      = b * (k1 * m * k1⁻¹) * b⁻¹ := by rw [← hk0ind _ hm1]
    _ = b * (b' * m * b'⁻¹) * b⁻¹ := by rw [← hk1ind m hm]
    _ = (b * b') * m * (b * b')⁻¹ := by group
    _ = (b' * b) * m * (b' * b)⁻¹ := by rw [hbb']
    _ = b' * (b * m * b⁻¹) * b'⁻¹ := by group
    _ = b' * (k0 * m * k0⁻¹) * b'⁻¹ := by rw [hk0ind m hm]
    _ = k1 * (k0 * m * k0⁻¹) * k1⁻¹ := by rw [hk1ind _ hm0]

private theorem r4l_commutator_pow {G : Type} [Group G] {x y z : G}
    (hz : z = x * y * x⁻¹ * y⁻¹) (hzx : z * x = x * z) :
    ∀ n : ℕ, x ^ n * y * (x ^ n)⁻¹ * y⁻¹ = z ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hxz : x * z ^ n = z ^ n * x := by
      have hcomm : Commute z x := hzx
      exact (hcomm.pow_left n).symm
    calc x ^ (n + 1) * y * (x ^ (n + 1))⁻¹ * y⁻¹
        = x * (x ^ n * y * (x ^ n)⁻¹ * y⁻¹) * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by
            rw [pow_succ']; group
      _ = x * z ^ n * x⁻¹ * (x * y * x⁻¹ * y⁻¹) := by rw [ih]
      _ = x * z ^ n * x⁻¹ * z := by rw [← hz]
      _ = z ^ n * z := by rw [hxz]; group
      _ = z ^ (n + 1) := by rw [pow_succ]

private theorem r4l_k0_mem_centralizer {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hZ : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g))
    (hInn : ∀ b ∈ Bs, ∃ k ∈ X, ∀ l ∈ X, b * l * b⁻¹ = k * l * k⁻¹)
    {b : G} (hb : b ∈ Bs) {k0 : G} (hk0X : k0 ∈ X) (hk0p : k0 ^ p = 1)
    (hk0ind : ∀ l ∈ X, b * l * b⁻¹ = k0 * l * k0⁻¹) :
    k0 ∈ Subgroup.centralizer (Bs : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b' hb'
  obtain ⟨k1, hk1X, _, hk1ind⟩ := r4l_exists_k0 hBs hZ hInn hb'
  have hc'C : k1⁻¹ * b' ∈ Subgroup.centralizer (X : Set G) :=
    r4l_inv_mul_mem_centralizer hk1ind
  have hbb' : b * b' = b' * b := by
    have h := hBs.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩
    exact congrArg Subtype.val h
  have hk0c' : k0 * (k1⁻¹ * b') = (k1⁻¹ * b') * k0 :=
    Subgroup.mem_centralizer_iff.mp hc'C k0 hk0X
  let z : G := k0 * k1 * k0⁻¹ * k1⁻¹
  have hzX : z ∈ X := by
    dsimp [z]
    exact X.mul_mem (X.mul_mem (X.mul_mem hk0X hk1X) (X.inv_mem hk0X)) (X.inv_mem hk1X)
  have hact := r4l_actions_comm hk0X hk1X hk0ind hk1ind hbb'
  have hzC : z ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1m : k0⁻¹ * k1⁻¹ ∈ X := X.mul_mem (X.inv_mem hk0X) (X.inv_mem hk1X)
    have h2m : k0⁻¹ * k1⁻¹ * l ∈ X := X.mul_mem h1m hl
    have h3m : k0⁻¹ * k1⁻¹ * l * k1 ∈ X := X.mul_mem h2m hk1X
    have hm : k0⁻¹ * k1⁻¹ * l * k1 * k0 ∈ X := X.mul_mem h3m hk0X
    have h := hact (k0⁻¹ * k1⁻¹ * l * k1 * k0) hm
    have hz_conj : z * l * z⁻¹ = l := by
      calc z * l * z⁻¹
          = k0 * (k1 * (k0⁻¹ * k1⁻¹ * l * k1 * k0) * k1⁻¹) * k0⁻¹ := by
              dsimp [z]; group
        _ = k1 * (k0 * (k0⁻¹ * k1⁻¹ * l * k1 * k0) * k0⁻¹) * k1⁻¹ := h
        _ = l := by group
    have hzl : z * l = l * z := by
      calc z * l = (z * l * z⁻¹) * z := by group
        _ = l * z := by rw [hz_conj]
    exact hzl.symm
  have hz_center : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC l l.2
  have hzxp : z * k0 = k0 * z :=
    (Subgroup.mem_centralizer_iff.mp hzC k0 hk0X).symm
  have hzp : z ^ p = 1 := by
    have hcomp := r4l_commutator_pow (x := k0) (y := k1) (z := z) rfl hzxp p
    simpa [hk0p] using hcomp.symm
  have hzord : orderOf (⟨z, hzX⟩ : ↥X) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hzp
  have hz_cop : Nat.Coprime p (orderOf (⟨z, hzX⟩ : ↥X)) := hZ _ hz_center
  have hz1 : z = 1 := by
    have h1 : orderOf (⟨z, hzX⟩ : ↥X) = 1 := by
      apply Nat.dvd_one.mp
      have h2 : orderOf (⟨z, hzX⟩ : ↥X) ∣ p.gcd (orderOf (⟨z, hzX⟩ : ↥X)) :=
        Nat.dvd_gcd hzord (dvd_refl _)
      rwa [Nat.Coprime.gcd_eq_one hz_cop] at h2
    have h2 : (⟨z, hzX⟩ : ↥X) = 1 := by
      rw [← orderOf_eq_one_iff]
      exact h1
    exact congrArg Subtype.val h2
  have hk0k1 : k0 * k1 = k1 * k0 := by
    have h := hz1
    dsimp [z] at h
    rw [show k0 * k1 * k0⁻¹ * k1⁻¹ = (k0 * k1) * (k1 * k0)⁻¹ by group] at h
    exact mul_inv_eq_one.mp h
  calc b' * k0 = (k1 * (k1⁻¹ * b')) * k0 := by group
    _ = k1 * ((k1⁻¹ * b') * k0) := by group
    _ = k1 * (k0 * (k1⁻¹ * b')) := by rw [hk0c']
    _ = (k1 * k0) * (k1⁻¹ * b') := by group
    _ = (k0 * k1) * (k1⁻¹ * b') := by rw [hk0k1]
    _ = k0 * (k1 * (k1⁻¹ * b')) := by group
    _ = k0 * b' := by group

private theorem r4l_exists_k0_BX {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZ : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g))
    (hInn : ∀ b ∈ Bs, ∃ k ∈ X, ∀ l ∈ X, b * l * b⁻¹ = k * l * k⁻¹)
    {b : G} (hb : b ∈ Bs) :
    ∃ k0 ∈ Bs ⊓ X, ∀ l ∈ X, b * l * b⁻¹ = k0 * l * k0⁻¹ := by
  obtain ⟨k0, hk0X, hk0p, hk0ind⟩ := r4l_exists_k0 hBs hZ hInn hb
  have hk0C : k0 ∈ Subgroup.centralizer (Bs : Set G) :=
    r4l_k0_mem_centralizer hBs hZ hInn hb hk0X hk0p hk0ind
  have hk0Bs : k0 ∈ Bs := hSC k0 hk0C hk0p
  exact ⟨k0, Subgroup.mem_inf.mpr ⟨hk0Bs, hk0X⟩, hk0ind⟩


private theorem r4l_mulAut_ext_of_agree {G : Type} [Group G] {Bs A B : Subgroup G}
    (hA : A ≤ Bs) (hB : B ≤ Bs) (hsup : Bs = A ⊔ B)
    {φ ψ : MulAut ↥Bs}
    (hφA : ∀ a : ↥A, φ ⟨a, hA a.2⟩ = ψ ⟨a, hA a.2⟩)
    (hφB : ∀ b : ↥B, φ ⟨b, hB b.2⟩ = ψ ⟨b, hB b.2⟩) : φ = ψ := by
  let K : Subgroup ↥Bs :=
    { carrier := {x | φ x = ψ x}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, map_mul, hx, hy]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_inv, map_inv, hx] }
  have hAK : A.subgroupOf Bs ≤ K := by
    intro x hx
    have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
    show φ x = ψ x
    have hx' : (⟨(x : G), hA hxA⟩ : ↥Bs) = x := Subtype.ext rfl
    rw [← hx']
    exact hφA ⟨(x : G), hxA⟩
  have hBK : B.subgroupOf Bs ≤ K := by
    intro x hx
    have hxB : (x : G) ∈ B := Subgroup.mem_subgroupOf.mp hx
    show φ x = ψ x
    have hx' : (⟨(x : G), hB hxB⟩ : ↥Bs) = x := Subtype.ext rfl
    rw [← hx']
    exact hφB ⟨(x : G), hxB⟩
  have htop : K = ⊤ := by
    have hle : A.subgroupOf Bs ⊔ B.subgroupOf Bs ≤ K := sup_le hAK hBK
    have hgen : A.subgroupOf Bs ⊔ B.subgroupOf Bs = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hA hB, ← hsup, Subgroup.subgroupOf_self]
    rw [hgen] at hle
    exact eq_top_iff.mpr hle
  apply MulEquiv.ext
  intro x
  have hx : x ∈ K := by rw [htop]; exact Subgroup.mem_top x
  change φ x = ψ x at hx
  exact hx

theorem ggLemma47c {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hZ : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g))
    (hInn : ∀ b ∈ Bs, ∃ k ∈ X, ∀ l ∈ X, b * l * b⁻¹ = k * l * k⁻¹) :
    Bs = (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) ∧
      (Bs ⊓ X) ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      (∀ e ∈ X, e ∈ Subgroup.centralizer ((Bs ⊓ X : Subgroup G) : Set G) → e ^ p = 1 →
        e ∈ Bs ⊓ X) ∧
      Subgroup.normalizer (Bs : Set G) ⊓ X =
        Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) ⊓ X ∧
      Nat.card (ggAutomizer X Bs) = Nat.card (ggAutomizer X (Bs ⊓ X)) := by
  have hsup : Bs = (Bs ⊓ X) ⊔ (Bs ⊓ Subgroup.centralizer (X : Set G)) := by
    apply le_antisymm
    · intro b hb
      obtain ⟨k0, hk0BX, hk0ind⟩ := r4l_exists_k0_BX hBs hSC hZ hInn hb
      have hk0Bs : k0 ∈ Bs := (Subgroup.mem_inf.mp hk0BX).1
      have hc : k0⁻¹ * b ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact Bs.mul_mem (Bs.inv_mem hk0Bs) hb
        · exact r4l_inv_mul_mem_centralizer hk0ind
      have hb_eq : b = k0 * (k0⁻¹ * b) := by group
      rw [hb_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk0BX) (Subgroup.mem_sup_right hc)
    · exact sup_le (inf_le_left : Bs ⊓ X ≤ Bs)
        (inf_le_left : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Bs)
  have hdisj : (Bs ⊓ X) ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have hgBX : g ∈ Bs ⊓ X := (Subgroup.mem_inf.mp hg).1
    have hgC : g ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_inf.mp hg).2
    have hgB : g ∈ Bs := (Subgroup.mem_inf.mp hgBX).1
    have hgX : g ∈ X := (Subgroup.mem_inf.mp hgBX).2
    have hgcenter : (⟨g, hgX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hgC l l.2
    have hgp : g ^ p = 1 := hBs.2 g hgB
    have hgpX : (⟨g, hgX⟩ : ↥X) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hgp]
    have hgord : orderOf (⟨g, hgX⟩ : ↥X) ∣ p := orderOf_dvd_of_pow_eq_one hgpX
    have hgcop : Nat.Coprime p (orderOf (⟨g, hgX⟩ : ↥X)) := hZ _ hgcenter
    have hgoo : orderOf (⟨g, hgX⟩ : ↥X) = 1 := by
      apply Nat.dvd_one.mp
      have h1 : orderOf (⟨g, hgX⟩ : ↥X) ∣ p.gcd (orderOf (⟨g, hgX⟩ : ↥X)) :=
        Nat.dvd_gcd hgord (dvd_refl _)
      rwa [Nat.Coprime.gcd_eq_one hgcop] at h1
    have h2 : (⟨g, hgX⟩ : ↥X) = 1 := by
      rw [← orderOf_eq_one_iff]
      exact hgoo
    exact congrArg Subtype.val h2
  have hSCX : ∀ e ∈ X, e ∈ Subgroup.centralizer ((Bs ⊓ X : Subgroup G) : Set G) → e ^ p = 1 →
      e ∈ Bs ⊓ X := by
    intro e heX heC hep
    let K : Subgroup G := Subgroup.centralizer ({e} : Set G)
    have hBX : (Bs ⊓ X : Subgroup G) ≤ K := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (Subgroup.mem_centralizer_iff.mp heC b hb).symm
    have hC : (Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ K := by
      intro c hc
      have hcX : c ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_inf.mp hc).2
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact Subgroup.mem_centralizer_iff.mp hcX e heX
    have hBsK : Bs ≤ K := by
      rw [hsup]
      exact sup_le hBX hC
    have heBsC : e ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hbK := hBsK hb
      rw [Subgroup.mem_centralizer_iff] at hbK
      exact (hbK e (Set.mem_singleton e)).symm
    have heBs : e ∈ Bs := hSC e heBsC hep
    exact Subgroup.mem_inf.mpr ⟨heBs, heX⟩
  have hnorm : Subgroup.normalizer (Bs : Set G) ⊓ X =
      Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) ⊓ X := by
    apply le_antisymm
    · intro n hn
      have hnX : n ∈ X := (Subgroup.mem_inf.mp hn).2
      have hnN : n ∈ Subgroup.normalizer (Bs : Set G) := (Subgroup.mem_inf.mp hn).1
      refine Subgroup.mem_inf.mpr ⟨?_, hnX⟩
      rw [Subgroup.mem_normalizer_iff] at hnN ⊢
      intro b
      constructor
      · intro hb
        have hbB : b ∈ Bs := (Subgroup.mem_inf.mp hb).1
        have hbX : b ∈ X := (Subgroup.mem_inf.mp hb).2
        exact Subgroup.mem_inf.mpr ⟨(hnN b).mp hbB,
          X.mul_mem (X.mul_mem hnX hbX) (X.inv_mem hnX)⟩
      · intro hb
        have hbB : n * b * n⁻¹ ∈ Bs := (Subgroup.mem_inf.mp hb).1
        have hbX : n * b * n⁻¹ ∈ X := (Subgroup.mem_inf.mp hb).2
        have hbX' : b ∈ X := by
          have h := X.mul_mem (X.mul_mem (X.inv_mem hnX) hbX) hnX
          rwa [show n⁻¹ * (n * b * n⁻¹) * n = b by group] at h
        exact Subgroup.mem_inf.mpr ⟨(hnN b).mpr hbB, hbX'⟩
    · intro n hn
      have hnX : n ∈ X := (Subgroup.mem_inf.mp hn).2
      have hnN : n ∈ Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) :=
        (Subgroup.mem_inf.mp hn).1
      refine Subgroup.mem_inf.mpr ⟨?_, hnX⟩
      apply mem_normalizer_iff_map_conj.mpr
      rw [hsup, Subgroup.map_sup]
      congr 1
      · exact mem_normalizer_iff_map_conj.mp hnN
      · apply le_antisymm
        · intro y hy
          rw [Subgroup.mem_map] at hy
          obtain ⟨c, hc, rfl⟩ := hy
          have hcX : c ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_inf.mp hc).2
          have hcn : n * c * n⁻¹ = c := by
            have h := Subgroup.mem_centralizer_iff.mp hcX n hnX
            calc n * c * n⁻¹ = c * n * n⁻¹ := by rw [h]
              _ = c := by group
          change n * c * n⁻¹ ∈ _
          rw [hcn]
          exact hc
        · intro c hc
          rw [Subgroup.mem_map]
          have hcX : c ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_inf.mp hc).2
          have hcn : n * c * n⁻¹ = c := by
            have h := Subgroup.mem_centralizer_iff.mp hcX n hnX
            calc n * c * n⁻¹ = c * n * n⁻¹ := by rw [h]
              _ = c := by group
          exact ⟨c, hc, hcn⟩
  have hAX : Bs ⊓ X ≤ Bs := inf_le_left
  have hCX : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Bs := inf_le_left
  let n_of : ↥(ggAutomizer X Bs) → G := fun φ =>
    Classical.choose (mem_ggAutomizer_iff.mp φ.2)
  have spec_of : ∀ φ : ↥(ggAutomizer X Bs),
      (n_of φ) ∈ X ∧ (n_of φ) ∈ Subgroup.normalizer (Bs : Set G) ∧
        ∀ b : ↥Bs, ((φ.1 b : ↥Bs) : G) = (n_of φ) * b * (n_of φ)⁻¹ :=
    fun φ => Classical.choose_spec (mem_ggAutomizer_iff.mp φ.2)
  let Φ : ↥(ggAutomizer X Bs) → ↥(ggAutomizer X (Bs ⊓ X)) := fun φ => by
    have hnBX : (n_of φ) ∈ Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) := by
      have h : (n_of φ) ∈ Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) ⊓ X := by
        rw [← hnorm]
        exact Subgroup.mem_inf.mpr ⟨(spec_of φ).2.1, (spec_of φ).1⟩
      exact (Subgroup.mem_inf.mp h).1
    exact ⟨ggConjAut (Bs ⊓ X) hnBX,
      ggConjAut_mem_ggAutomizer (spec_of φ).1 hnBX⟩
  have Φ_inj : Function.Injective Φ := by
    intro φ ψ hΦ
    have hAgreeBX : ∀ b : ↥(Bs ⊓ X),
        (n_of φ) * (b : G) * (n_of φ)⁻¹ = (n_of ψ) * (b : G) * (n_of ψ)⁻¹ := by
      intro b
      have h := congrArg (fun f : MulAut ↥(Bs ⊓ X) => ((f b : ↥(Bs ⊓ X)) : G))
        (congrArg Subtype.val hΦ)
      have h1 : ((Φ φ).1 b : G) = (n_of φ) * (b : G) * (n_of φ)⁻¹ := rfl
      have h2 : ((Φ ψ).1 b : G) = (n_of ψ) * (b : G) * (n_of ψ)⁻¹ := rfl
      rw [h1, h2] at h
      exact h
    have hφψ : φ.1 = ψ.1 := by
      apply r4l_mulAut_ext_of_agree (A := Bs ⊓ X)
        (B := Bs ⊓ Subgroup.centralizer (X : Set G)) inf_le_left inf_le_left hsup
      · intro a
        apply Subtype.ext
        rw [(spec_of φ).2.2 ⟨a, hAX a.2⟩,
          (spec_of ψ).2.2 ⟨a, hAX a.2⟩]
        exact hAgreeBX a
      · intro c
        apply Subtype.ext
        have hcX : (c : G) ∈ Subgroup.centralizer (X : Set G) := (Subgroup.mem_inf.mp c.2).2
        have hcφ : (n_of φ) * (c : G) * (n_of φ)⁻¹ = (c : G) := by
          have h := Subgroup.mem_centralizer_iff.mp hcX (n_of φ) (spec_of φ).1
          calc (n_of φ) * (c : G) * (n_of φ)⁻¹
              = (c : G) * (n_of φ) * (n_of φ)⁻¹ := by rw [h]
            _ = (c : G) := by group
        have hcψ : (n_of ψ) * (c : G) * (n_of ψ)⁻¹ = (c : G) := by
          have h := Subgroup.mem_centralizer_iff.mp hcX (n_of ψ) (spec_of ψ).1
          calc (n_of ψ) * (c : G) * (n_of ψ)⁻¹
              = (c : G) * (n_of ψ) * (n_of ψ)⁻¹ := by rw [h]
            _ = (c : G) := by group
        rw [(spec_of φ).2.2 ⟨c, hCX c.2⟩,
          (spec_of ψ).2.2 ⟨c, hCX c.2⟩, hcφ, hcψ]
    exact Subtype.ext hφψ
  have Φ_surj : Function.Surjective Φ := by
    intro ψ
    obtain ⟨n, hnX, hnN, hψn⟩ := mem_ggAutomizer_iff.mp ψ.2
    have hnBs : n ∈ Subgroup.normalizer (Bs : Set G) := by
      have h : n ∈ Subgroup.normalizer (Bs : Set G) ⊓ X := by
        rw [hnorm]
        exact Subgroup.mem_inf.mpr ⟨hnN, hnX⟩
      exact (Subgroup.mem_inf.mp h).1
    let φ : ↥(ggAutomizer X Bs) :=
      ⟨ggConjAut Bs hnBs, ggConjAut_mem_ggAutomizer hnX hnBs⟩
    refine ⟨φ, ?_⟩
    apply Subtype.ext
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    have hleft : ((Φ φ).1 b : G) = (n_of φ) * (b : G) * (n_of φ)⁻¹ := rfl
    have hright : ((ψ.1 b : ↥(Bs ⊓ X)) : G) = n * (b : G) * n⁻¹ := hψn b
    rw [hleft, hright]
    have h1 : ((φ.1 ⟨b, hAX b.2⟩ : ↥Bs) : G) =
        (n_of φ) * (b : G) * (n_of φ)⁻¹ := (spec_of φ).2.2 ⟨b, hAX b.2⟩
    have h2 : ((φ.1 ⟨b, hAX b.2⟩ : ↥Bs) : G) = n * (b : G) * n⁻¹ := by
      change ((ggConjAut Bs hnBs ⟨b, hAX b.2⟩ : ↥Bs) : G) = n * (b : G) * n⁻¹
      exact ggConjAut_apply Bs hnBs ⟨b, hAX b.2⟩
    rw [← h1, h2]
  exact ⟨hsup, hdisj, hSCX, hnorm,
    Nat.card_congr (Equiv.ofBijective Φ ⟨Φ_inj, Φ_surj⟩)⟩

end CFSG.StandardType
