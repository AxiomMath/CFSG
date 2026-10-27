module

public import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.RankThree.PartTwo.Sec20.SimsYKO3

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem relIndex_centralizer_le_two_mul {S V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVS : V ≤ S) (hA : IsElemAbelian 2 A) (hAS : A ≤ S)
    (hm : ∀ B : Subgroup G, B ≤ S → IsElemAbelian 2 B → Nat.card B ≤ 2 * Nat.card A) :
    (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤
      2 * (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
  set C : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G)
  have hCA : C ≤ A := inf_le_left
  have hCV : ∀ x ∈ C, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 hx.2 y hy).symm
  have hB : IsElemAbelian 2 (C ⊔ V) := (hA.mono hCA).sup_of_commute hV hCV
  have hBc : Nat.card (C ⊔ V : Subgroup G) ≤ 2 * Nat.card A :=
    hm _ (sup_le (hCA.trans hAS) hVS) hB
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C V hCV).1
  have hCVeq : C ⊓ V = A ⊓ V := by
    refine le_antisymm (inf_le_inf_right V hCA) fun x hx => ⟨⟨hx.1, ?_⟩, hx.2⟩
    exact Subgroup.mem_centralizer_iff.2 fun y hy => hV.comm hy hx.2
  rw [hCVeq] at hprod
  have hle : A ⊓ V ≤ V ⊓ Subgroup.centralizer (A : Set G) := fun x hx =>
    ⟨hx.2, Subgroup.mem_centralizer_iff.2 fun a ha => hA.comm ha hx.1⟩
  have hne : (A ⊓ V).relIndex V ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 := Subgroup.relIndex_le_of_le_left hle hne
  rw [Subgroup.inf_relIndex_right] at h1
  have hv : A.relIndex V * Nat.card (A ⊓ V : Subgroup G) = Nat.card V :=
    Subgroup.relIndex_mul_card A V
  have hc : C.relIndex A * Nat.card C = Nat.card A := by
    have := Subgroup.relIndex_mul_card C A
    rwa [inf_eq_left.2 hCA] at this
  have hd : 0 < Nat.card (A ⊓ V : Subgroup G) := Nat.card_pos
  have hcpos : 0 < Nat.card C := Nat.card_pos
  have hb : Nat.card (C ⊔ V : Subgroup G) = Nat.card C * A.relIndex V := by
    apply Nat.eq_of_mul_eq_mul_right hd
    rw [hprod, ← hv]
    ring
  have h2 : Nat.card C * A.relIndex V ≤ Nat.card C * (2 * C.relIndex A) :=
    calc Nat.card C * A.relIndex V = Nat.card (C ⊔ V : Subgroup G) := hb.symm
      _ ≤ 2 * Nat.card A := hBc
      _ = Nat.card C * (2 * C.relIndex A) := by rw [← hc]; ring
  exact h1.trans (Nat.le_of_mul_le_mul_left h2 hcpos)

theorem relIndex_centralizer_le_sq {V : Subgroup G} {e y : G}
    (hy : y ∈ Subgroup.normalizer (V : Set G)) (he2 : e * e = 1) (hey : e * y * e⁻¹ = y⁻¹)
    {n : ℕ} (hn : Odd n)
    (hyn : y ^ n ∈ Subgroup.centralizer (V : Set G)) :
    (V ⊓ Subgroup.centralizer ({y} : Set G)).relIndex V ≤
      ((V ⊓ Subgroup.centralizer ({e} : Set G)).relIndex V) ^ 2 := by
  have hee : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have h1 : e * y⁻¹ * e = y := by
    rw [hee] at hey
    calc e * y⁻¹ * e = (e * y * e)⁻¹ := by simp [mul_inv_rev, hee, mul_assoc]
      _ = y := by rw [hey, inv_inv]
  have hprod : e * (y⁻¹ * e * y) = y * y :=
    calc e * (y⁻¹ * e * y) = (e * y⁻¹ * e) * y := by simp [mul_assoc]
      _ = y * y := by rw [h1]
  set X : Subgroup G := V ⊓ Subgroup.centralizer ({e} : Set G)
  set X' : Subgroup G := V ⊓ Subgroup.centralizer ({y⁻¹ * e * y} : Set G)
  set Y : Subgroup G := V ⊓ Subgroup.centralizer ({y} : Set G)
  have hXX' : X ⊓ X' ≤ Y := by
    rintro v ⟨⟨hvV, hve⟩, -, hve'⟩
    refine ⟨hvV, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hve : v * e = e * v := Subgroup.mem_centralizer_singleton_iff.1 hve
    have hve' : v * (y⁻¹ * e * y) = (y⁻¹ * e * y) * v :=
      Subgroup.mem_centralizer_singleton_iff.1 hve'
    have hvyy : v * (y * y) = (y * y) * v := by
      rw [← hprod]
      calc v * (e * (y⁻¹ * e * y)) = (v * e) * (y⁻¹ * e * y) := (mul_assoc v e _).symm
        _ = (e * v) * (y⁻¹ * e * y) := by rw [hve]
        _ = e * (v * (y⁻¹ * e * y)) := mul_assoc e v _
        _ = e * ((y⁻¹ * e * y) * v) := by rw [hve']
        _ = e * (y⁻¹ * e * y) * v := (mul_assoc e _ v).symm
    obtain ⟨m, rfl⟩ := hn
    have hc2 : Commute v ((y * y) ^ m) := (show Commute v (y * y) from hvyy).pow_right m
    have hc3 : Commute v (y ^ (2 * m + 1)) := Subgroup.mem_centralizer_iff.1 hyn v hvV
    have hyeq : y = ((y * y) ^ m)⁻¹ * y ^ (2 * m + 1) := by
      rw [pow_succ, pow_mul, pow_two, inv_mul_cancel_left]
    have hcy : Commute v (((y * y) ^ m)⁻¹ * y ^ (2 * m + 1)) := hc2.inv_right.mul_right hc3
    rw [← hyeq] at hcy
    exact hcy
  have hXX'eq : X'.relIndex V = X.relIndex V := by
    have hfV : V.map (MulAut.conj y : G →* G) = V := Subgroup.mem_normalizer_iff_map_conj_eq.1 hy
    have hcomap : X.comap (MulAut.conj y : G →* G) = X' := by
      ext z
      show y * z * y⁻¹ ∈ X ↔ z ∈ X'
      constructor
      · rintro ⟨hzV, hze⟩
        refine ⟨(Subgroup.mem_normalizer_iff.1 hy z).2 hzV,
          Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have h := Subgroup.mem_centralizer_singleton_iff.1 hze
        calc z * (y⁻¹ * e * y) = y⁻¹ * (y * z * y⁻¹ * e) * y := by group
          _ = y⁻¹ * (e * (y * z * y⁻¹)) * y := by rw [h]
          _ = (y⁻¹ * e * y) * z := by group
      · rintro ⟨hzV, hze⟩
        refine ⟨(Subgroup.mem_normalizer_iff.1 hy z).1 hzV,
          Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have h := Subgroup.mem_centralizer_singleton_iff.1 hze
        calc y * z * y⁻¹ * e = y * (z * (y⁻¹ * e * y)) * y⁻¹ := by group
          _ = y * ((y⁻¹ * e * y) * z) * y⁻¹ := by rw [h]
          _ = e * (y * z * y⁻¹) := by group
    have := Subgroup.relIndex_comap X (MulAut.conj y : G →* G) V
    rw [hcomap, hfV] at this
    exact this
  have hne : (X ⊓ X').relIndex V ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc Y.relIndex V ≤ (X ⊓ X').relIndex V := Subgroup.relIndex_le_of_le_left hXX' hne
    _ ≤ X.relIndex V * X'.relIndex V := Subgroup.relIndex_inf_le
    _ = (X.relIndex V) ^ 2 := by rw [hXX'eq, pow_two]

theorem mem_centralizer_of_stab {V C : Subgroup G} (hV : IsElemAbelian 2 V) (hCV : C ≤ V)
    {w : G} (hwC : ∀ c ∈ C, w * c = c * w) (hwV : ∀ v ∈ V, w * v * w⁻¹ * v⁻¹ ∈ C)
    {n : ℕ} (hn : Odd n) (hwn : w ^ n ∈ Subgroup.centralizer (V : Set G)) :
    w ∈ Subgroup.centralizer (V : Set G) := by
  refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
  obtain ⟨c, hc⟩ : ∃ c : G, c = w * v * w⁻¹ * v⁻¹ := ⟨_, rfl⟩
  have hcC : c ∈ C := hc ▸ hwV v hv
  have hwc : Commute w c := hwC c hcC
  have hwv : w * v * w⁻¹ = c * v := by rw [hc]; group
  have hpow : ∀ i : ℕ, w ^ i * v * (w ^ i)⁻¹ = c ^ i * v := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have hwci : w * c ^ i * w⁻¹ = c ^ i := by
        rw [(hwc.pow_right i).eq, mul_inv_cancel_right]
      calc w ^ (i + 1) * v * (w ^ (i + 1))⁻¹
          = w * (w ^ i * v * (w ^ i)⁻¹) * w⁻¹ := by rw [pow_succ']; group
        _ = w * (c ^ i * v) * w⁻¹ := by rw [ih]
        _ = (w * c ^ i * w⁻¹) * (w * v * w⁻¹) := by group
        _ = c ^ (i + 1) * v := by rw [hwci, hwv, pow_succ, mul_assoc]
  have hcn : c ^ n = 1 := by
    have h1 : w ^ n * v * (w ^ n)⁻¹ = v := by
      have h2 : v * w ^ n = w ^ n * v := Subgroup.mem_centralizer_iff.1 hwn v hv
      rw [← h2, mul_inv_cancel_right]
    have h3 := hpow n
    rw [h1] at h3
    exact mul_eq_right.1 h3.symm
  have hc2 : c ^ 2 = 1 := by rw [pow_two]; exact hV.mul_self_eq_one (hCV hcC)
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, hc2, one_pow, one_mul] at hcn
  have hwv' : w * v = v * w := by
    have h := hcn
    rw [hc, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h
  exact hwv'.symm

theorem not_dvd_card_mulAut_of_card_le {U : Type*} [Group U] [Finite U]
    (hUc : ∀ a b : U, a * b = b * a) (hU2 : ∀ a : U, a ^ 2 = 1) (hcard : Nat.card U ≤ 2 ^ 8) :
    ¬ 5 ^ 3 ∣ Nat.card (MulAut U) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 U := fun a => ⟨1, by simpa using hU2 a⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hn8 : n ≤ 8 := by
    have h : 2 ^ n ≤ 2 ^ 8 := hn ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hUc hU2 hn
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  interval_cases n <;> decide

private theorem exists_secAction {V C N : Subgroup G} [(C.subgroupOf V).Normal]
    (hNV : N ≤ Subgroup.normalizer (V : Set G)) (hNC : N ≤ Subgroup.normalizer (C : Set G)) :
    ∃ ρ : N →* MulAut (↥V ⧸ C.subgroupOf V), ∀ (g : N) (x y : ↥V), (y : G) = g * x * g⁻¹ →
      ρ g (QuotientGroup.mk x) = QuotientGroup.mk y := by
  let ρ₀ : N →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hNV)
  have hρ₀ : ∀ (g : N) (x : ↥V), ((ρ₀ g x : ↥V) : G) = g * x * g⁻¹ := fun g x => rfl
  have hmap : ∀ g : N, (C.subgroupOf V).map (ρ₀ g : ↥V →* ↥V) = C.subgroupOf V := by
    intro g
    ext z
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact (Subgroup.mem_normalizer_iff.1 (hNC g.2) x).1 hx
    · intro hz
      refine ⟨ρ₀ g⁻¹ z, ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hz ⊢
        exact (Subgroup.mem_normalizer_iff.1 (hNC (g⁻¹).2) z).1 hz
      · show ρ₀ g (ρ₀ g⁻¹ z) = z
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  refine ⟨{ toFun := fun g => QuotientGroup.congr (C.subgroupOf V) (C.subgroupOf V) (ρ₀ g) (hmap g)
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    show QuotientGroup.mk (ρ₀ 1 x) = QuotientGroup.mk x
    rw [map_one]
    rfl
  · intro g h
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    show QuotientGroup.mk (ρ₀ (g * h) x) = QuotientGroup.mk (ρ₀ g (ρ₀ h x))
    rw [map_mul]
    rfl
  · intro g x y hy
    show QuotientGroup.mk (ρ₀ g x) = QuotientGroup.mk y
    congr 1
    exact Subtype.ext (by rw [hρ₀, hy])

theorem false_of_five_cube {V W : Subgroup G} {k : G} (hV : IsElemAbelian 2 V)
    (hWV : W ≤ Subgroup.normalizer (V : Set G)) (hkV : k ∈ Subgroup.normalizer (V : Set G))
    (hkW : k ∈ Subgroup.normalizer (W : Set G))
    (hW5 : ∀ w ∈ W, ∃ a : ℕ, w ^ (5 ^ a) ∈ Subgroup.centralizer (V : Set G))
    (hk5 : ∃ b : ℕ, k ^ (5 ^ b) ∈ Subgroup.centralizer (V : Set G))
    (hidx : (V ⊓ Subgroup.centralizer (W : Set G)).relIndex V ≤ 2 ^ 8)
    (h25 : 25 ≤ (W ⊓ Subgroup.centralizer (V : Set G)).relIndex W)
    (hk : ∀ w ∈ W, ¬ ∀ x ∈ W,
      (k * w⁻¹) * x * (k * w⁻¹)⁻¹ * x⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    False := by
  haveI : IsMulCommutative ↥V := hV.1
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set C : Subgroup G := V ⊓ Subgroup.centralizer (W : Set G)
  have hCV : C ≤ V := inf_le_left
  have hCW : ∀ c ∈ C, ∀ w ∈ W, w * c = c * w := fun c hc w hw =>
    Subgroup.mem_centralizer_iff.1 hc.2 w hw
  have hWC : W ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.le_centralizer_iff.2 inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hcen : ∀ {g : G}, g ∈ Subgroup.normalizer (W : Set G) → ∀ h : G,
      h ∈ Subgroup.centralizer (W : Set G) → g * h * g⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
    intro g hg h hh
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : g⁻¹ * w * g ∈ W := (Subgroup.mem_normalizer_iff''.1 hg w).1 hw
    have h1 := Subgroup.mem_centralizer_iff.1 hh _ hw'
    calc w * (g * h * g⁻¹) = g * ((g⁻¹ * w * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
      _ = (g * h * g⁻¹) * w := by group
  have hkC : k ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨hhV, hhc⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hkV h).1 hhV, hcen hkW h hhc⟩
    · rintro ⟨hhV, hhc⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hkV h).2 hhV, ?_⟩
      have h1 := hcen (Subgroup.inv_mem _ hkW) _ hhc
      have h2 : k⁻¹ * (k * h * k⁻¹) * k⁻¹⁻¹ = h := by group
      rwa [h2] at h1
  set N₁ : Subgroup G := Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (C : Set G)
  have hWN : W ≤ N₁ := le_inf hWV hWC
  have hkN : k ∈ N₁ := ⟨hkV, hkC⟩
  obtain ⟨ρ, hρ⟩ := exists_secAction (V := V) (C := C) (N := N₁) inf_le_left inf_le_right
  have hker : ∀ g : N₁, ρ g = 1 ↔ ∀ v ∈ V, (g : G) * v * (g : G)⁻¹ * v⁻¹ ∈ C := by
    intro g
    have hmem : ∀ v ∈ V, (g : G) * v * (g : G)⁻¹ ∈ V := fun v hv =>
      (Subgroup.mem_normalizer_iff.1 g.2.1 v).1 hv
    constructor
    · intro h v hv
      have h1 := hρ g ⟨v, hv⟩ ⟨_, hmem v hv⟩ rfl
      rw [h, MulAut.one_apply] at h1
      have h2 := QuotientGroup.eq.1 h1
      rw [Subgroup.mem_subgroupOf] at h2
      have h3 : v⁻¹ * ((g : G) * v * (g : G)⁻¹) = (g : G) * v * (g : G)⁻¹ * v⁻¹ :=
        hV.comm (inv_mem hv) (hmem v hv)
      exact h3 ▸ h2
    · intro h
      refine MulEquiv.ext fun x => ?_
      induction x using QuotientGroup.induction_on with | H x => ?_
      rw [hρ g x ⟨_, hmem x x.2⟩ rfl, MulAut.one_apply]
      refine (QuotientGroup.eq.2 ?_).symm
      rw [Subgroup.mem_subgroupOf]
      have h3 : (x : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) = (g : G) * x * (g : G)⁻¹ * (x : G)⁻¹ :=
        hV.comm (inv_mem x.2) (hmem x x.2)
      show (x : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) ∈ C
      rw [h3]
      exact h x x.2
  let ι : ↥W →* ↥N₁ := Subgroup.inclusion hWN
  let ρW : ↥W →* MulAut (↥V ⧸ C.subgroupOf V) := ρ.comp ι
  have hW1 : ∀ w : ↥W, ρW w = 1 ↔ (w : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro w
    constructor
    · intro h
      obtain ⟨a, ha⟩ := hW5 w w.2
      exact mem_centralizer_of_stab hV hCV (fun c hc => hCW c hc w w.2)
        ((hker (ι w)).1 h) (Odd.pow (by decide)) ha
    · intro h
      refine (hker (ι w)).2 fun v hv => ?_
      have h1 : v * (w : G) = (w : G) * v := Subgroup.mem_centralizer_iff.1 h v hv
      have h2 : (w : G) * v * (w : G)⁻¹ * v⁻¹ = 1 := by rw [← h1]; group
      exact h2 ▸ one_mem C
  have hrange : 25 ≤ Nat.card ρW.range := by
    have hkerW : ρW.ker = (W ⊓ Subgroup.centralizer (V : Set G)).subgroupOf W := by
      ext w
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hW1 w]
      exact ⟨fun h => ⟨w.2, h⟩, fun h => h.2⟩
    rw [← Subgroup.index_ker, hkerW]
    exact h25
  have hP5 : IsPGroup 5 ρW.range := by
    rintro ⟨_, w, rfl⟩
    obtain ⟨a, ha⟩ := hW5 w w.2
    refine ⟨a, Subtype.ext ?_⟩
    show (ρW w) ^ 5 ^ a = 1
    rw [← map_pow]
    exact (hW1 (w ^ 5 ^ a)).2 ha
  let k' : ↥N₁ := ⟨k, hkN⟩
  have hK5 : IsPGroup 5 (Subgroup.zpowers (ρ k')) := by
    obtain ⟨b, hb⟩ := hk5
    have hρk : (ρ k') ^ 5 ^ b = 1 := by
      rw [← map_pow]
      refine (hker _).2 fun v hv => ?_
      have h1 : v * k ^ 5 ^ b = k ^ 5 ^ b * v := Subgroup.mem_centralizer_iff.1 hb v hv
      have h2 : k ^ 5 ^ b * v * (k ^ 5 ^ b)⁻¹ * v⁻¹ = 1 := by rw [← h1]; group
      exact h2 ▸ one_mem C
    exact IsPGroup.of_card_dvd_pow (n := b)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hρk)
  have hconj : ∀ g : ↥N₁, (g : G) ∈ Subgroup.normalizer (W : Set G) →
      ∀ x ∈ ρW.range, ρ g * x * (ρ g)⁻¹ ∈ ρW.range := by
    rintro g hg _ ⟨w, rfl⟩
    refine ⟨⟨(g : G) * w * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.1 hg w).1 w.2⟩, ?_⟩
    show ρ (ι _) = ρ g * ρ (ι w) * (ρ g)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hnorm : ρ k' ∈ Subgroup.normalizer (ρW.range : Set (MulAut (↥V ⧸ C.subgroupOf V))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj k' hkW x
    · intro hx
      have h1 := hconj k'⁻¹ (Subgroup.inv_mem _ hkW) _ hx
      have h2 : ρ k'⁻¹ * (ρ k' * x * (ρ k')⁻¹) * (ρ k'⁻¹)⁻¹ = x := by
        rw [map_inv]; group
      rwa [h2] at h1
  have hnot : ρ k' ∉ ρW.range := by
    rintro ⟨w, hw⟩
    refine hk w w.2 fun x hx => ?_
    have hρg : ρ (k' * (ι w)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      show ρ k' * (ρW w)⁻¹ = 1
      rw [hw, mul_inv_cancel]
    have hzW : (k * (w : G)⁻¹) * x * (k * (w : G)⁻¹)⁻¹ * x⁻¹ ∈ W := by
      have h1 : k * ((w : G)⁻¹ * x * w) * k⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.1 hkW _).1 (mul_mem (mul_mem (inv_mem w.2) hx) w.2)
      have h2 : (k * (w : G)⁻¹) * x * (k * (w : G)⁻¹)⁻¹ = k * ((w : G)⁻¹ * x * w) * k⁻¹ := by
        group
      rw [h2]
      exact mul_mem h1 (inv_mem hx)
    refine (hW1 ⟨_, hzW⟩).1 ?_
    have heq : ι ⟨_, hzW⟩ = (k' * (ι w)⁻¹) * ι ⟨x, hx⟩ * (k' * (ι w)⁻¹)⁻¹ * (ι ⟨x, hx⟩)⁻¹ :=
      Subtype.ext rfl
    show ρ (ι _) = 1
    rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, hρg]
    simp
  set Γ : Subgroup (MulAut (↥V ⧸ C.subgroupOf V)) := ρW.range ⊔ Subgroup.zpowers (ρ k')
  have hΓ5 : IsPGroup 5 Γ :=
    hP5.to_sup_of_normal_left' hK5 (Subgroup.zpowers_le.2 hnorm)
  have hlt : ρW.range < Γ := by
    refine lt_of_le_of_ne le_sup_left fun h => hnot ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨t, ht⟩ := hΓ5.exists_card_eq
  have hcl : Nat.card ρW.range < Nat.card Γ := Subgroup.card_lt_of_lt hlt
  have ht3 : 3 ≤ t := by
    by_contra hlt3
    have h5 : 5 ^ t ≤ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 5 ^ 3 ∣ Nat.card (MulAut (↥V ⧸ C.subgroupOf V)) :=
    (pow_dvd_pow 5 ht3).trans (ht ▸ Subgroup.card_subgroup_dvd_card Γ)
  have hUc : ∀ a b : ↥V ⧸ C.subgroupOf V, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hV.comm a.2 b.2)
  have hU2 : ∀ a : ↥V ⧸ C.subgroupOf V, a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with | H a => ?_
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext (hV.2 a a.2)
  exact not_dvd_card_mulAut_of_card_le hUc hU2 hidx hdvd

end CFSG.RankThree.PartTwo.Sec20.SimsYKO3
