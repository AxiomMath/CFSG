module

public import CFSG.Quasithin.H13.L32NLem14325b
public import CFSG.Quasithin.H13.L32NLem14325a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

variable {G : Type} [Group G]

theorem mem_conjugate_iff {X : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate X g ↔ g * x * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

theorem conjugate_eq_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : CFSG.conjugate X g = X := by
  ext x
  rw [mem_conjugate_iff]
  exact (Subgroup.mem_normalizer_iff.mp hg x).symm

theorem comm_of_mem_conj {T V : Subgroup G} {g x : G}
    (hx : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g) {z : G}
    (hz : z ∈ centerOf (fsuU T V) ⊓ CFSG.conjugate (fsuU T V) g) : x * z = z * x := by
  have hx' := mem_conjugate_iff.mp hx
  have hz' := mem_conjugate_iff.mp hz.2
  have hc := Subgroup.mem_centralizer_iff.mp hx'.2 _ hz'
  calc x * z = g⁻¹ * ((g * x * g⁻¹) * (g * z * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * z * g⁻¹) * (g * x * g⁻¹)) * g := by rw [← hc]
    _ = z * x := by group

variable [Finite G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

namespace Ctx14325

variable (C : Ctx14325 G T L V V₂ g D)
include C

theorem relIndex_inf_conj (h12810 : Lemma12_8_10) :
    (centerOf (fsuU T V) ⊓ CFSG.conjugate (fsuU T V) g).relIndex (centerOf (fsuU T V)) =
      Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) := by
  obtain ⟨h1, h2, -, -, -, h6⟩ := h12810 G T L V 3 (fsuV1 T V) V₂ C.setting g C.gP C.gN
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := h6
  set ZI := centerOf (i128 T L V (fsuV1 T V)) with hZI
  set Zg := CFSG.conjugate (centerOf (fsuU T V)) g with hZg
  have heq : Zg ⊓ centralizerMod (centerOf (fsuU T V)) (l32nH T V) (fsuU T V) =
      ZI ⊔ CFSG.conjugate (fsuV1 T V) g := by
    rw [e1, e2, e3, e4, e5]
  have hN : Zg ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    C.zUg_le.trans (L14332.l32nH_le_normalizer_fsuU T V)
  have hker : ∀ x ∈ Zg, (∃ hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G),
      D.ρ ⟨x, hxN⟩ = 1) ↔ x ∈ ZI ⊔ CFSG.conjugate (fsuV1 T V) g := by
    intro x hx
    rw [← heq]
    constructor
    · rintro ⟨hxN, h1⟩
      refine Subgroup.mem_inf.mpr ⟨hx, C.zUg_le hx,
        L14332.normalizer_le_normalizer_centerOf _ hxN, fun u hu => ?_⟩
      exact (L128A.HatU.rho_eq_one_iff D ⟨x, hxN⟩).mp h1 u hu
    · intro h1
      obtain ⟨-, ⟨-, -, h2⟩⟩ := Subgroup.mem_inf.mp h1
      exact ⟨hN hx, (L128A.HatU.rho_eq_one_iff D ⟨x, hN hx⟩).mpr h2⟩
  rw [L128A.HatU.card_img_eq_relIndex D hN hker]
  have hgI : g ∈ Subgroup.normalizer (ZI : Set G) :=
    L14332.normalizer_le_normalizer_centerOf _ (le_normalizer_conjClosure _ _ C.gP)
  have hconj : CFSG.conjugate (ZI ⊔ fsuV1 T V) g = ZI ⊔ CFSG.conjugate (fsuV1 T V) g := by
    unfold CFSG.conjugate
    rw [Subgroup.map_sup]
    congr 1
    have := conjugate_eq_of_mem_normalizer hgI
    unfold CFSG.conjugate at this
    exact this
  have hZ0 : centerOf (fsuU T V) ⊓ CFSG.conjugate (fsuU T V) g = ZI ⊔ fsuV1 T V := by
    change zU128 V (fsuV1 T V) ⊓ CFSG.conjugate (u128 V (fsuV1 T V)) g = ZI ⊔ fsuV1 T V
    rw [h1, h2]
  rw [hZ0, ← hconj, hZg]
  unfold CFSG.conjugate
  rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]

theorem relIndex_centralizer_le (h12810 : Lemma12_8_10) {x : G}
    (hx : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g) :
    (vH T L V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (vH T L V) ≤
      Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) := by
  set Z₀ := centerOf (fsuU T V) ⊓ CFSG.conjugate (fsuU T V) g with hZ₀
  have hle : vH T L V ⊓ Z₀ ≤ vH T L V ⊓ Subgroup.centralizer ({x} : Set G) := by
    rintro z ⟨hzV, hzZ⟩
    refine ⟨hzV, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (comm_of_mem_conj hx hzZ).symm
  rw [← C.relIndex_inf_conj h12810]
  calc (vH T L V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (vH T L V)
      ≤ (vH T L V ⊓ Z₀).relIndex (vH T L V) :=
        Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
    _ = Z₀.relIndex (vH T L V) := by rw [inf_comm, Subgroup.inf_relIndex_right]
    _ ≤ Z₀.relIndex (centerOf (fsuU T V)) :=
        Subgroup.relIndex_le_of_le_right C.vH_le Subgroup.index_ne_zero_of_finite

theorem exists_of_mem_hatV {w : D.V} (hw : w ∈ D.hat V) : ∃ v ∈ V, D.π v = w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨v, ⟨hv, -⟩, rfl⟩ := hw
    exact ⟨v, hv, rfl⟩
  | zero => exact ⟨1, V.one_mem, D.π_one⟩
  | add w w' _ _ ih ih' =>
    obtain ⟨v, hv, rfl⟩ := ih
    obtain ⟨v', hv', rfl⟩ := ih'
    exact ⟨v * v', V.mul_mem hv hv', D.π_mul v (C.V_U hv) v' (C.V_U hv')⟩
  | smul r w _ ih =>
    obtain ⟨v, hv, rfl⟩ := ih
    rcases (show ∀ r : ZMod 2, r = 0 ∨ r = 1 by decide) r with rfl | rfl
    · exact ⟨1, V.one_mem, by rw [zero_smul, D.π_one]⟩
    · exact ⟨v, hv, by rw [one_smul]⟩

theorem rho_mem_hatV_of_normalizer {h : G} (hh : h ∈ l32nH T V)
    (hhV : h ∈ Subgroup.normalizer (V : Set G)) {w : D.V} (hw : w ∈ D.hat V) :
    D.ρ ⟨h, L14332.l32nH_le_normalizer_fsuU T V hh⟩ w ∈ D.hat V := by
  obtain ⟨v, hv, rfl⟩ := C.exists_of_mem_hatV hw
  rw [D.ρ_π _ v (C.V_U hv)]
  have hv' : h * v * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hhV v).mp hv
  exact Submodule.subset_span ⟨h * v * h⁻¹, ⟨hv', C.V_U hv'⟩, rfl⟩

theorem rho_mem_hatV {h : G} (hh : h ∈ l32nH T V)
    (hc : h ∈ Subgroup.centralizer (vH T L V : Set G)) {w : D.V} (hw : w ∈ D.hat V) :
    D.ρ ⟨h, L14332.l32nH_le_normalizer_fsuU T V hh⟩ w ∈ D.hat V := by
  have hM : h ∈ l32nH T V ⊓ Subgroup.normalizer (L : Set G) := ⟨hh, C.cent_le hc⟩
  rw [C.HM] at hM
  exact C.rho_mem_hatV_of_normalizer hh hM.2 hw

end Ctx14325

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

omit [Finite G] in
theorem fix_of_maps_card_four {S : Submodule (ZMod 2) W} (hS : Nat.card S = 4) {p k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {γ : W ≃ₗ[ZMod 2] W} (hγ : γ ^ (p ^ k) = 1)
    (hγS : ∀ s ∈ S, γ s ∈ S) : ∀ s ∈ S, γ s = s := by
  have : Finite (S : Set W) := Set.Finite.to_subtype (Set.toFinite _)
  have hcard : Nat.card (S : Set W) < p := by
    have : Nat.card (S : Set W) = Nat.card S := rfl
    omega
  have h := smul_eq_of_pow_prime (g := γ) (S := (S : Set W)) hp hcard hγS
    (fun b _ => by rw [hγ, one_smul])
  exact h

theorem eq_one_of_fix_card_sixteen (hW : Nat.card W = 16) {γ : W ≃ₗ[ZMod 2] W} {k : ℕ}
    (hγ : γ ^ (5 ^ k) = 1) {w : W} (hw0 : w ≠ 0) (hw : γ w = w) : γ = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.zpowers γ) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp
      (orderOf_dvd_of_pow_eq_one hγ)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hmod := hP.card_modEq_card_fixedPoints W
  let F : AddSubgroup W :=
    { carrier := {v | γ v = v}
      add_mem' := fun {a b} (ha : γ a = a) (hb : γ b = b) => show γ (a + b) = a + b by
        rw [map_add, ha, hb]
      zero_mem' := map_zero γ
      neg_mem' := fun {a} (ha : γ a = a) => show γ (-a) = -a by rw [map_neg, ha] }
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers γ) W) = Nat.card F := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro hv
      exact hv ⟨γ, Subgroup.mem_zpowers γ⟩
    · intro hv g
      have hle : Subgroup.zpowers γ ≤ MulAction.stabilizer (W ≃ₗ[ZMod 2] W) v :=
        (Subgroup.zpowers_le).mpr (MulAction.mem_stabilizer_iff.mpr hv)
      exact MulAction.mem_stabilizer_iff.mp (hle g.2)
  rw [hfix, hW] at hmod
  have hdvd : Nat.card F ∣ 16 := hW ▸ AddSubgroup.card_addSubgroup_dvd_card F
  have h2 : 2 ≤ Nat.card F := by
    have h0 : (0 : W) ∈ F := F.zero_mem
    have hw' : w ∈ F := hw
    have : Finite F := inferInstance
    exact Finite.one_lt_card_iff_nontrivial.mpr
      ⟨⟨⟨0, h0⟩, ⟨w, hw'⟩, fun h => hw0 (congrArg Subtype.val h).symm⟩⟩
  have hF16 : Nat.card F = 16 := by
    have hle : Nat.card F ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    have hdivs : Nat.card F ∈ Nat.divisors 16 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by decide] at hdivs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdivs
    unfold Nat.ModEq at hmod
    omega
  have htop : F = ⊤ := AddSubgroup.eq_top_of_card_eq F (by rw [hF16, hW])
  ext v
  have : v ∈ F := htop ▸ AddSubgroup.mem_top v
  exact this

end L14325

end CFSG.Quasithin.H13
