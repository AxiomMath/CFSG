module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

private lemma eq_one_of_mem_centralizer_of_center_eq_bot_inner {G : Type} [Group G] {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) {z : G} (hzX : z ∈ X)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) : z = 1 := by
  have hz : (⟨z, hzX⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  have hz1 : (⟨z, hzX⟩ : X) ∈ (⊥ : Subgroup X) := by
    rw [← hX]
    exact hz
  simpa using Subgroup.mem_bot.mp hz1

private lemma eq_of_conj_eq_of_center_eq_bot_inner {G : Type} [Group G] {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) {u v : G} (huX : u ∈ X) (hvX : v ∈ X)
    (h : ∀ y ∈ X, u * y * u⁻¹ = v * y * v⁻¹) : u = v := by
  have huvX : u⁻¹ * v ∈ X := X.mul_mem (X.inv_mem huX) hvX
  have huvC : u⁻¹ * v ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    calc y * (u⁻¹ * v) = u⁻¹ * (u * y * u⁻¹) * v := by group
      _ = u⁻¹ * (v * y * v⁻¹) * v := by rw [h y hy]
      _ = (u⁻¹ * v) * y := by group
  have h1 : u⁻¹ * v = 1 := eq_one_of_mem_centralizer_of_center_eq_bot_inner hX huvX huvC
  calc u = u * 1 := by group
    _ = u * (u⁻¹ * v) := by rw [← h1]
    _ = v := by group

private lemma mem_sup_of_commute {G : Type} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    ∀ x : G, x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  let T : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨h1, hh1, k1, hk1, rfl⟩ := ha
        obtain ⟨h2, hh2, k2, hk2, rfl⟩ := hb
        refine ⟨h1 * h2, H.mul_mem hh1 hh2, k1 * k2, K.mul_mem hk1 hk2, ?_⟩
        calc h1 * h2 * (k1 * k2) = h1 * (h2 * k1) * k2 := by group
          _ = h1 * (k1 * h2) * k2 := by rw [hc h2 hh2 k1 hk1]
          _ = h1 * k1 * (h2 * k2) := by group
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by group⟩
      inv_mem' := by
        intro a ha
        obtain ⟨h, hh, k, hk, rfl⟩ := ha
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        rw [mul_inv_rev]
        exact hc h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk) }
  have hHT : H ≤ T := fun h hh => ⟨h, hh, 1, K.one_mem, by group⟩
  have hKT : K ≤ T := fun k hk => ⟨1, H.one_mem, k, hk, by group⟩
  have hEq : H ⊔ K = T := le_antisymm (sup_le hHT hKT) (by
    rintro x ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup hh hk)
  intro x
  rw [hEq]
  constructor <;> intro hx <;> exact hx

private lemma card_sup_of_disjoint_of_commute {G : Type} [Group G] {H K : Subgroup G}
    (hd : Disjoint H K) (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : ↥H × ↥K → ↥(H ⊔ K) :=
    fun q => ⟨(q.1 : G) * (q.2 : G), Subgroup.mul_mem_sup q.1.2 q.2.2⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨h, hh⟩, ⟨k, hk⟩⟩ ⟨⟨h', hh'⟩, ⟨k', hk'⟩⟩ heq
    have he : h * k = h' * k' := by simpa [f] using congrArg Subtype.val heq
    have hz : h'⁻¹ * h = k' * k⁻¹ := by
      calc h'⁻¹ * h = h'⁻¹ * (h * k) * k⁻¹ := by group
        _ = h'⁻¹ * (h' * k') * k⁻¹ := by rw [he]
        _ = k' * k⁻¹ := by group
    have hzH : h'⁻¹ * h ∈ H := H.mul_mem (H.inv_mem hh') hh
    have hzK : h'⁻¹ * h ∈ K := by rw [hz]; exact K.mul_mem hk' (K.inv_mem hk)
    have hz1 : h'⁻¹ * h = 1 := by
      have hmem : h'⁻¹ * h ∈ H ⊓ K := ⟨hzH, hzK⟩
      rw [disjoint_iff.mp hd] at hmem
      simpa using hmem
    have hheq : h = h' := (inv_mul_eq_one.mp hz1).symm
    have hkeq : k = k' := by
      apply mul_left_cancel (a := h)
      rw [← hheq] at he
      exact he
    exact Prod.ext (Subtype.ext hheq) (Subtype.ext hkeq)
  have hf_surj : Function.Surjective f := by
    intro z
    obtain ⟨h, hh, k, hk, hk_eq⟩ := (mem_sup_of_commute hc (z : G)).mp z.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hk_eq⟩
  have hcard := Nat.card_eq_of_bijective f ⟨hf_inj, hf_surj⟩
  rw [Nat.card_prod] at hcard
  exact hcard.symm

structure GGHalfInnerPart {G : Type} [Group G] (Bs K' J TJ : Subgroup G) (x y' : G)
    (τ : ↥Bs →* ↥K') (kx : G) : Prop where
  act : ∀ (b : ↥Bs) (l : G), l ∈ K' → (b : G) * l * (b : G)⁻¹ = (τ b : G) * l * (τ b : G)⁻¹
  mem_Bs : ∀ b : ↥Bs, (τ b : G) ∈ Bs
  kx_def : ∀ hx : x ∈ Bs, (τ ⟨x, hx⟩ : G) = kx
  y'_triv : ∀ hy : y' ∈ Bs, τ ⟨y', hy⟩ = 1
  kx_mem : kx ∈ K'
  kx_order : orderOf kx = 3
  B1_eq : Bs ⊓ K' = Subgroup.zpowers kx ⊔ TJ
  disj : Disjoint (Subgroup.zpowers kx) TJ
  norm : ∀ m' ∈ K', m' ∈ Subgroup.normalizer ((Subgroup.zpowers kx ⊔ TJ : Subgroup G) : Set G) →
    m' ∈ Subgroup.normalizer (Bs : Set G)
  equivariant : ∀ m' ∈ K', m' ∈ Subgroup.normalizer (Bs : Set G) → ∀ b b' : ↥Bs,
    (b' : G) = m' * b * m'⁻¹ → (τ b' : G) = m' * (τ b : G) * m'⁻¹
  J_comp : IsComponentOf J (K' ⊓ Subgroup.centralizer ({kx} : Set G))

theorem GGHalfJoin.innerPart {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y' : G} {K' TJ : Subgroup G} {k : ℕ}
    (hcfg : GGConfig 3 B Bs x L D J) (hnbr' : GGNbr 3 B x D J y' K') (hJK' : J ≤ K')
    (hZ : Subgroup.center ↥K' = ⊥) (hnorm : Bs ≤ Subgroup.normalizer (K' : Set G))
    (hinn : ∀ b ∈ Bs, ∃ c ∈ K', ∀ l ∈ K', b * l * b⁻¹ = c * l * c⁻¹)
    (hk : 1 ≤ k) (hcard : Nat.card Bs = 3 ^ (k + 1)) (hTJ : TJ ≤ Bs ⊓ J)
    (hTJcard : Nat.card TJ = 3 ^ (k - 1)) (hZJ : Subgroup.center ↥J = ⊥) :
    ∃ (τ : ↥Bs →* ↥K') (kx : G), GGHalfInnerPart Bs K' J TJ x y' τ kx := by
  have hBs : GGBstar 3 B Bs := hcfg.2.1
  obtain ⟨-, -, -, -, -, -, hS, -⟩ := hcfg.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  have hxBs : x ∈ Bs := hcfg.2.1.1 (hcfg.2.2.1.1 hcfg.2.2.1.2.2.2.1)
  have hJc : IsComponentOf J (K' ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hS hDJ hnbr' hJK'
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := hJc.1.trans inf_le_right
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  let τfun : ↥Bs → ↥K' := fun b =>
    ⟨Classical.choose (hinn b b.2), (Classical.choose_spec (hinn b b.2)).1⟩
  have hτ_spec : ∀ (b : ↥Bs) (l : G), l ∈ K' →
      (b : G) * l * (b : G)⁻¹ = (τfun b : G) * l * (τfun b : G)⁻¹ :=
    fun b l hl => (Classical.choose_spec (hinn b b.2)).2 l hl
  have hτ_eq : ∀ (b : ↥Bs) (c : K'),
      (∀ l ∈ K', (b : G) * l * (b : G)⁻¹ = (c : G) * l * (c : G)⁻¹) → τfun b = c := by
    intro b c hc
    exact Subtype.ext (eq_of_conj_eq_of_center_eq_bot_inner hZ (τfun b).2 c.2
      (fun l hl => (hτ_spec b l hl).symm.trans (hc l hl)))
  have hτ_one : τfun 1 = 1 := by
    apply hτ_eq
    intro l hl
    simp
  have hτ_mul : ∀ a b : ↥Bs, τfun (a * b) = τfun a * τfun b := by
    intro a b
    apply hτ_eq
    intro l hl
    have hbact : (b : G) * l * (b : G)⁻¹ = (τfun b : G) * l * (τfun b : G)⁻¹ := hτ_spec b l hl
    calc ((a * b : ↥Bs) : G) * l * ((a * b : ↥Bs) : G)⁻¹
        = (a : G) * ((b : G) * l * (b : G)⁻¹) * (a : G)⁻¹ := by
          rw [Subgroup.coe_mul]; group
      _ = (a : G) * ((τfun b : G) * l * (τfun b : G)⁻¹) * (a : G)⁻¹ := by rw [hbact]
      _ = (τfun a : G) * ((τfun b : G) * l * (τfun b : G)⁻¹) * (τfun a : G)⁻¹ :=
          hτ_spec a ((τfun b : G) * l * (τfun b : G)⁻¹)
            (K'.mul_mem (K'.mul_mem (τfun b).2 hl) (K'.inv_mem (τfun b).2))
      _ = ((τfun a * τfun b : ↥K') : G) * l * ((τfun a * τfun b : ↥K') : G)⁻¹ := by
          simp only [Subgroup.coe_mul]
          group
  let τ : ↥Bs →* ↥K' := { toFun := τfun, map_one' := hτ_one, map_mul' := hτ_mul }
  let kx : G := (τ ⟨x, hxBs⟩ : G)
  have hτ_mem : ∀ b : ↥Bs, (τfun b : G) ∈ Bs := by
    intro b
    obtain ⟨x₁, hx₁, c, hc, hb⟩ :=
      ggBstar_split_of_inner (X := K') hBs hZ hnorm hinn (b : G) b.2
    have hx₁K : x₁ ∈ K' := hx₁.2
    have hcx : ∀ l ∈ K', (b : G) * l * (b : G)⁻¹ = x₁ * l * x₁⁻¹ := by
      intro l hl
      have hcc : c * l * c⁻¹ = l := by
        have hcomm : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc.2 l hl
        calc c * l * c⁻¹ = (l * c) * c⁻¹ := by rw [hcomm]
          _ = l := by group
      calc (b : G) * l * (b : G)⁻¹ = (x₁ * c) * l * (x₁ * c)⁻¹ := by rw [hb]
        _ = x₁ * (c * l * c⁻¹) * x₁⁻¹ := by group
        _ = x₁ * l * x₁⁻¹ := by rw [hcc]
    have heq : τfun b = ⟨x₁, hx₁K⟩ := hτ_eq b ⟨x₁, hx₁K⟩ hcx
    rw [heq]
    exact hx₁.1
  have hkx_mem : kx ∈ K' := (τ ⟨x, hxBs⟩).2
  have hkxBs : kx ∈ Bs := hτ_mem ⟨x, hxBs⟩
  have hkx_def : ∀ hx : x ∈ Bs, (τ ⟨x, hx⟩ : G) = kx := by
    intro hx
    exact congrArg (fun b : ↥Bs => (τ b : G)) (Subtype.ext rfl)
  have hy'_triv : ∀ hy : y' ∈ Bs, τ ⟨y', hy⟩ = 1 := by
    intro hy
    apply hτ_eq
    intro l hl
    have hcomm : l * y' = y' * l :=
      Subgroup.mem_centralizer_singleton_iff.mp (hnbr'.1.2.2.2.1 hl)
    show (y' : G) * l * (y' : G)⁻¹ = ((1 : ↥K') : G) * l * ((1 : ↥K') : G)⁻¹
    rw [← hcomm]
    simp
  have hkx_pow : kx ^ 3 = 1 := hBs.2.1.2 kx hkxBs
  have hkx_ne : kx ≠ 1 := by
    intro hkx1
    apply hnbr'.2.2.2
    have hcomm : ∀ k ∈ K', x * k = k * x := by
      intro k hk
      have hact : x * k * x⁻¹ = kx * k * kx⁻¹ := hτ_spec ⟨x, hxBs⟩ k hk
      have hxk : x * k * x⁻¹ = k := by rw [hact, hkx1]; group
      calc x * k = (x * k * x⁻¹) * x := by group
        _ = k * x := by rw [hxk]
    have hbot : (⁅K', Subgroup.zpowers x⁆ : Subgroup G) = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcomm k hk).symm
    rw [hbot]
    exact bot_le
  have hkx_order : orderOf kx = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hkx_pow hkx_ne
  have hkx_comm_J : ∀ j ∈ J, kx * j = j * kx := by
    intro j hj
    have hjK : j ∈ K' := hJK' hj
    have hjx : j * x = x * j := Subgroup.mem_centralizer_singleton_iff.mp (hJx hj)
    have hact : x * j * x⁻¹ = kx * j * kx⁻¹ := hτ_spec ⟨x, hxBs⟩ j hjK
    have hxj : x * j * x⁻¹ = j := by
      calc x * j * x⁻¹ = (j * x) * x⁻¹ := by rw [hjx]
        _ = j := by group
    rw [hxj] at hact
    calc kx * j = (kx * j * kx⁻¹) * kx := by group
      _ = j * kx := by rw [← hact]
  have hkx_notJ : kx ∉ J := by
    intro hkxJ
    have hcenter : (⟨kx, hkxJ⟩ : J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      exact (hkx_comm_J (j : G) j.2).symm
    have hmem : (⟨kx, hkxJ⟩ : J) ∈ (⊥ : Subgroup ↥J) := by rw [← hZJ]; exact hcenter
    have h1 : kx = 1 := by
      simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    exact hkx_ne h1
  have hdisjJ : Subgroup.zpowers kx ⊓ J = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    have hgJ : g ∈ J := hg.2
    have hcenter : (⟨g, hgJ⟩ : J) ∈ Subgroup.center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro j
      apply Subtype.ext
      change (j : G) * g = g * (j : G)
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg.1
      rw [← hi]
      exact (Commute.zpow_left (show Commute kx (j : G) from hkx_comm_J (j : G) j.2) i).eq.symm
    have hmem : (⟨g, hgJ⟩ : J) ∈ (⊥ : Subgroup ↥J) := by rw [← hZJ]; exact hcenter
    have hg1 : g = 1 := by
      simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
    exact Subgroup.mem_bot.mpr hg1
  have hTJleJ : TJ ≤ J := fun t ht => (hTJ ht).2
  have hdisj : Disjoint (Subgroup.zpowers kx) TJ := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro g hg
    have hgJ : g ∈ Subgroup.zpowers kx ⊓ J := ⟨hg.1, hTJleJ hg.2⟩
    rw [hdisjJ] at hgJ
    exact hgJ
  have hHle : Subgroup.zpowers kx ≤ Bs ⊓ K' := by
    rw [Subgroup.zpowers_le]
    exact ⟨hkxBs, hkx_mem⟩
  have hTJle : TJ ≤ Bs ⊓ K' := by
    intro t ht
    exact ⟨(hTJ ht).1, hJK' (hTJ ht).2⟩
  have hle : Subgroup.zpowers kx ⊔ TJ ≤ Bs ⊓ K' := sup_le hHle hTJle
  have hcomm_sup : ∀ h ∈ Subgroup.zpowers kx, ∀ t ∈ TJ, h * t = t * h := by
    intro h hh t ht
    exact CFSG.Open.IsElemAbelian.comm hBs.2.1 (hHle hh).1 (hTJ ht).1
  have hcardsup : Nat.card ↥(Subgroup.zpowers kx ⊔ TJ) = 3 ^ (k' + 1) := by
    rw [card_sup_of_disjoint_of_commute hdisj hcomm_sup, Nat.card_zpowers, hkx_order, hTJcard]
    simp only [Nat.add_sub_cancel]
    rw [pow_succ]
    ring
  have hsplit := card_ggBstar_split (X := K') hBs hZ hnorm hinn
  have hmul : Nat.card ↥(Bs ⊓ K') *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) = 3 ^ (k' + 1 + 1) := by
    rw [← hsplit, hcard]
  have hy'C : y' ∈ Bs ⊓ Subgroup.centralizer (K' : Set G) := by
    refine ⟨hBs.1 hnbr'.1.2.1, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mp (hnbr'.1.2.2.2.1 hk))
  have hy'_ord : orderOf y' = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hBs.2.1.2 y' (hBs.1 hnbr'.1.2.1)) hnbr'.1.2.2.1
  have hCge : 3 ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) := by
    have hleC : Subgroup.zpowers y' ≤ Bs ⊓ Subgroup.centralizer (K' : Set G) := by
      rw [Subgroup.zpowers_le]; exact hy'C
    have hdvd : Nat.card ↥(Subgroup.zpowers y') ∣
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) := Subgroup.card_dvd_of_le hleC
    have hcardZ : Nat.card ↥(Subgroup.zpowers y') = 3 := by rw [Nat.card_zpowers, hy'_ord]
    rw [hcardZ] at hdvd
    haveI : Nonempty ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) := ⟨1⟩
    exact Nat.le_of_dvd (Nat.card_pos_iff.mpr ⟨inferInstance, inferInstance⟩) hdvd
  have hB1le : Nat.card ↥(Bs ⊓ K') ≤ 3 ^ (k' + 1) := by
    have hmul3 : Nat.card ↥(Bs ⊓ K') * 3 ≤ 3 ^ (k' + 1 + 1) := by
      calc Nat.card ↥(Bs ⊓ K') * 3
          ≤ Nat.card ↥(Bs ⊓ K') *
              Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) := Nat.mul_le_mul_left _ hCge
        _ = 3 ^ (k' + 1 + 1) := hmul
    rw [pow_succ] at hmul3
    exact Nat.le_of_mul_le_mul_right hmul3 (by norm_num : 0 < 3)
  have hcardB1 : Nat.card ↥(Bs ⊓ K') ≤ Nat.card ↥(Subgroup.zpowers kx ⊔ TJ) := by
    rw [hcardsup]; exact hB1le
  have hB1_eq : Bs ⊓ K' = Subgroup.zpowers kx ⊔ TJ :=
    (Subgroup.eq_of_le_of_card_ge hle hcardB1).symm
  have hfw : ∀ m' ∈ K', m' ∈ Subgroup.normalizer ((Subgroup.zpowers kx ⊔ TJ : Subgroup G) : Set G) →
      ∀ b ∈ Bs, m' * b * m'⁻¹ ∈ Bs := by
    intro m' hm'K hm'B1 b hb
    obtain ⟨x₁, hx₁, c, hc, hb_eq⟩ :=
      ggBstar_split_of_inner (X := K') hBs hZ hnorm hinn b hb
    have hm'x₁ : m' * x₁ * m'⁻¹ ∈ Subgroup.zpowers kx ⊔ TJ := by
      have hx₁B1 : x₁ ∈ Subgroup.zpowers kx ⊔ TJ := by rw [← hB1_eq]; exact hx₁
      exact (Subgroup.mem_normalizer_iff.mp hm'B1 x₁).mp hx₁B1
    have hcomm_c : m' * c * m'⁻¹ = c := by
      have hcomm : m' * c = c * m' := Subgroup.mem_centralizer_iff.mp hc.2 m' hm'K
      calc m' * c * m'⁻¹ = (c * m') * m'⁻¹ := by rw [hcomm]
        _ = c := by group
    have heq : m' * (x₁ * c) * m'⁻¹ = (m' * x₁ * m'⁻¹) * c := by
      rw [show m' * (x₁ * c) * m'⁻¹ =
          (m' * x₁ * m'⁻¹) * (m' * c * m'⁻¹) by group, hcomm_c]
    rw [hb_eq, heq]
    exact Bs.mul_mem (hle hm'x₁).1 hc.1
  have hnorm_field : ∀ m' ∈ K',
      m' ∈ Subgroup.normalizer ((Subgroup.zpowers kx ⊔ TJ : Subgroup G) : Set G) →
      m' ∈ Subgroup.normalizer (Bs : Set G) := by
    intro m' hm'K hm'B1
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb; exact hfw m' hm'K hm'B1 b hb
    · intro hb
      have hm'inv : m'⁻¹ ∈
          Subgroup.normalizer ((Subgroup.zpowers kx ⊔ TJ : Subgroup G) : Set G) :=
        (Subgroup.normalizer _).inv_mem hm'B1
      have hmem := hfw m'⁻¹ (K'.inv_mem hm'K) hm'inv (m' * b * m'⁻¹) hb
      have heq : m'⁻¹ * (m' * b * m'⁻¹) * m'⁻¹⁻¹ = b := by group
      rw [heq] at hmem
      exact hmem
  have hequiv : ∀ m' ∈ K', m' ∈ Subgroup.normalizer (Bs : Set G) → ∀ b b' : ↥Bs,
      (b' : G) = m' * b * m'⁻¹ → (τ b' : G) = m' * (τ b : G) * m'⁻¹ := by
    intro m' hm'K hm'Bs b b' hbb'
    have hmiddle : ∀ l ∈ K', (b' : G) * l * (b' : G)⁻¹ =
        (m' * (τfun b : G) * m'⁻¹) * l * (m' * (τfun b : G) * m'⁻¹)⁻¹ := by
      intro l hl
      have hmlK : m'⁻¹ * l * m' ∈ K' := K'.mul_mem (K'.mul_mem (K'.inv_mem hm'K) hl) hm'K
      have hact : (b : G) * (m'⁻¹ * l * m') * (b : G)⁻¹ =
          (τfun b : G) * (m'⁻¹ * l * m') * (τfun b : G)⁻¹ := hτ_spec b (m'⁻¹ * l * m') hmlK
      calc (b' : G) * l * (b' : G)⁻¹
          = m' * ((b : G) * (m'⁻¹ * l * m') * (b : G)⁻¹) * m'⁻¹ := by rw [hbb']; group
        _ = m' * ((τfun b : G) * (m'⁻¹ * l * m') * (τfun b : G)⁻¹) * m'⁻¹ := by rw [hact]
        _ = (m' * (τfun b : G) * m'⁻¹) * l * (m' * (τfun b : G) * m'⁻¹)⁻¹ := by group
    have hτb' := hτ_eq b' ⟨m' * (τfun b : G) * m'⁻¹,
        K'.mul_mem (K'.mul_mem hm'K (τfun b).2) (K'.inv_mem hm'K)⟩ hmiddle
    exact congrArg Subtype.val hτb'
  have hcent_eq : K' ⊓ Subgroup.centralizer ({kx} : Set G) =
      K' ⊓ Subgroup.centralizer ({x} : Set G) := by
    apply le_antisymm
    · intro l hl
      have hlK : l ∈ K' := hl.1
      have hlkx : l * kx = kx * l := Subgroup.mem_centralizer_singleton_iff.mp hl.2
      have hact : x * l * x⁻¹ = kx * l * kx⁻¹ := hτ_spec ⟨x, hxBs⟩ l hlK
      have hkxl : kx * l * kx⁻¹ = l := by
        calc kx * l * kx⁻¹ = (l * kx) * kx⁻¹ := by rw [hlkx]
          _ = l := by group
      have hxl : x * l = l * x := by
        calc x * l = (x * l * x⁻¹) * x := by group
          _ = l * x := by rw [hact, hkxl]
      exact ⟨hlK, Subgroup.mem_centralizer_singleton_iff.mpr hxl.symm⟩
    · intro l hl
      have hlK : l ∈ K' := hl.1
      have hlx : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.mp hl.2
      have hact : x * l * x⁻¹ = kx * l * kx⁻¹ := hτ_spec ⟨x, hxBs⟩ l hlK
      have hxl : x * l * x⁻¹ = l := by
        calc x * l * x⁻¹ = (l * x) * x⁻¹ := by rw [hlx]
          _ = l := by group
      have hkxl : kx * l * kx⁻¹ = l := by rw [← hact, hxl]
      have hkxl' : kx * l = l * kx := by
        calc kx * l = (kx * l * kx⁻¹) * kx := by group
          _ = l * kx := by rw [hkxl]
      exact ⟨hlK, Subgroup.mem_centralizer_singleton_iff.mpr hkxl'.symm⟩
  refine ⟨τ, kx, ?_⟩
  refine
    { act := fun b l hl => hτ_spec b l hl
      mem_Bs := hτ_mem
      kx_def := hkx_def
      y'_triv := hy'_triv
      kx_mem := hkx_mem
      kx_order := hkx_order
      B1_eq := hB1_eq
      disj := hdisj
      norm := hnorm_field
      equivariant := hequiv
      J_comp := ?_ }
  rw [hcent_eq]
  exact hJc

end CFSG.StandardType

end
