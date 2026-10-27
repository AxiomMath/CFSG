module

public import CFSG.Quasithin.Vol2.Ch10SecERho
public import CFSG.Quasithin.Vol2.Ch10SecFS1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv

theorem vFour_mul_self : ∀ σ ∈ SecE.vFour, σ * σ = 1 := by decide +kernel

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {hyp : Hyp10 G T L I} {t : G}
  (D : SecE.Case2Data hyp t)

theorem mul_self_eq_one_of_normalizes {W : Type*} [CommGroup W] {K P : Subgroup (MulAut W)}
    (θ : ↥K ≃* Perm (Fin 5)) (hP : ∀ g (hg : g ∈ K), g ∈ P ↔ θ ⟨g, hg⟩ ∈ SecE.eFour)
    {a : MulAut W} (ha : a ∈ oTwoUpper K) (hn : ∀ p ∈ P, a * p * a⁻¹ ∈ P) : a * a = 1 := by
  have haK := oTwoUpper_le _ ha
  have halt := SecE.mem_alternatingGroup_of_mem_oTwoUpper θ ha
  have hnorm : ∀ g ∈ SecE.eFour, θ ⟨a, haK⟩ * g * (θ ⟨a, haK⟩)⁻¹ ∈ SecE.eFour := by
    intro g hg
    have hp : (θ.symm g).1 ∈ P := (hP _ (θ.symm g).2).mpr (by simpa using hg)
    have h1 := hn _ hp
    have hK : a * (θ.symm g).1 * a⁻¹ ∈ K := K.mul_mem (K.mul_mem haK (θ.symm g).2) (K.inv_mem haK)
    have h2 := (hP _ hK).mp h1
    have e : (⟨a * (θ.symm g).1 * a⁻¹, hK⟩ : ↥K) = ⟨a, haK⟩ * θ.symm g * (⟨a, haK⟩)⁻¹ :=
      Subtype.ext rfl
    rwa [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
  have hv := SecE.mem_vFour_of_normalizes _ (Perm.mem_alternatingGroup.mp halt) hnorm
  have hsq := vFour_mul_self _ hv
  have h1 : (⟨a, haK⟩ : ↥K) * ⟨a, haK⟩ = 1 := θ.injective (by rw [map_mul, hsq, map_one])
  exact congrArg Subtype.val h1

include D in
theorem false_of_orderOf_eq_three
    (h1013 : Ch10.Stmt10_1_3) (h113 : ASInputs.AS_C_1_13)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h2 : Ch10.Case10_1_1Two T L I)
    (hb : IsShort2 L ∧ IsAltType L 5) (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G))
    {x : G} (hxM : x ∈ fsuM T L) (hxS : x ∈ Subgroup.normalizer (baum T : Set G))
    (hx3 : orderOf x = 3) : False := by
  have hV := SecA.isElemAbelian_fsuVM hyp
  have h3 : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    obtain ⟨e⟩ := h2.1
    rw [Nat.card_congr e.toEquiv, SecE.card_alt_five]
    norm_num
  have hxL0 : x ∈ fsuL0 T L := by
    rw [← h1013 G T L I hyp 3 Nat.prime_three (by norm_num) h3]
    exact Subgroup.subset_closure ⟨hxM, 1, by rw [hx3, pow_one]⟩
  have hxN : x ∈ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.fsuL0_le_normalizer_fsuVM T L I hxL0
  set xs := convI hV ⟨x, hxN⟩ with hxsdef
  have hxs : xs ∈ oTwoUpper D.K₁ ⊔ oTwoUpper D.K₂ := by
    rw [D.oTwo₁, D.oTwo₂, ← SecE.autI_fsuL0 h37 h38 hyp ht htn]
    exact convI_mem_autI hV hxL0 hxN
  have hcommK : ∀ a ∈ D.K₁, ∀ b ∈ D.K₂, b * a * b⁻¹ = a := fun a ha b hb => by
    rw [← D.comm a ha b hb]
    group
  have hBN : oTwoUpper D.K₂ ≤ Subgroup.normalizer (oTwoUpper D.K₁ : Set (MulAut _)) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [hcommK a (oTwoUpper_le _ ha) b (oTwoUpper_le _ hb)]
      exact ha
    · intro ha
      have h1 := hcommK _ (oTwoUpper_le _ ha) b⁻¹ (D.K₂.inv_mem (oTwoUpper_le _ hb))
      have e : a = b⁻¹ * (b * a * b⁻¹) * b⁻¹⁻¹ := by group
      rw [e, h1]
      exact ha
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left (oTwoUpper D.K₁) (oTwoUpper D.K₂) hBN
  have hxs' : xs ∈ (↑(oTwoUpper D.K₁ ⊔ oTwoUpper D.K₂) :
      Set (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)))) := hxs
  rw [hcoe] at hxs'
  obtain ⟨a, ha, b, hbO, hab⟩ := Set.mem_mul.mp hxs'
  have hxsJ : ∀ p ∈ autI hV (thompsonJ T), xs * p * xs⁻¹ ∈ autI hV (thompsonJ T) := by
    intro p hp
    rw [← D.baum_eq] at hp ⊢
    obtain ⟨s, hs, rfl⟩ := (mem_autI _).mp hp
    rw [mem_autI]
    refine ⟨⟨x, hxN⟩ * s * (⟨x, hxN⟩)⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp hxS s).mp hs
  have haK := oTwoUpper_le _ ha
  have hbK := oTwoUpper_le _ hbO
  have hP1 : ∀ p ∈ D.K₁ ⊓ autI hV (thompsonJ T),
      a * p * a⁻¹ ∈ D.K₁ ⊓ autI hV (thompsonJ T) := by
    intro p hp
    have e : a * p * a⁻¹ = xs * p * xs⁻¹ := by
      rw [← hab]
      calc a * p * a⁻¹ = a * (b * p * b⁻¹) * a⁻¹ := by rw [hcommK p hp.1 b hbK]
        _ = a * b * p * (a * b)⁻¹ := by group
    exact ⟨D.K₁.mul_mem (D.K₁.mul_mem haK hp.1) (D.K₁.inv_mem haK), e ▸ hxsJ p hp.2⟩
  have hcommK' : ∀ a ∈ D.K₁, ∀ b ∈ D.K₂, a * b * a⁻¹ = b := fun a ha b hb => by
    rw [D.comm a ha b hb]
    group
  have hP2 : ∀ p ∈ D.K₂ ⊓ autI hV (thompsonJ T),
      b * p * b⁻¹ ∈ D.K₂ ⊓ autI hV (thompsonJ T) := by
    intro p hp
    have hmem : b * p * b⁻¹ ∈ D.K₂ := D.K₂.mul_mem (D.K₂.mul_mem hbK hp.1) (D.K₂.inv_mem hbK)
    have e : b * p * b⁻¹ = xs * p * xs⁻¹ := by
      rw [← hab]
      calc b * p * b⁻¹ = a * (b * p * b⁻¹) * a⁻¹ := by rw [hcommK' a haK _ hmem]
        _ = a * b * p * (a * b)⁻¹ := by group
    exact ⟨hmem, e ▸ hxsJ p hp.2⟩
  have ha2 := mul_self_eq_one_of_normalizes D.θ₁ D.memP₁ ha hP1
  have hb2 := mul_self_eq_one_of_normalizes D.θ₂ D.memP₂ hbO hP2
  have hab' : a * b = b * a := D.comm a haK b hbK
  have hxs2 : xs * xs = 1 := by
    rw [← hab]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab']
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hx3' : (⟨x, hxN⟩ : Subgroup.normalizer (fsuVM T L I : Set G)) ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hx3]
    exact pow_orderOf_eq_one x
  have hxs3 : xs ^ 3 = 1 := by rw [hxsdef, ← map_pow, hx3', map_one]
  have hxs1 : xs = 1 := by
    have e : xs = xs ^ 3 * (xs * xs)⁻¹ := by group
    rw [e, hxs3, hxs2, inv_one, one_mul]
  have hxV : x ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
    (convI_eq_one_iff hV ⟨x, hxN⟩).mp hxs1
  have hxO : x ∈ pCoreOf 2 (fsuL0 T L ⊔ T) := by
    refine SecA.charTwo_L0T hyp ⟨le_sup_left (a := fsuL0 T L) hxL0, ?_⟩
    show x ∈ Subgroup.centralizer (pCoreOf 2 (fsuL0 T L ⊔ T) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [pCoreOf_L0T_eq_inf h37 h38 h3228 hyp (Or.inr h2)] at hy
    obtain ⟨v, hv, c, hc, rfl⟩ :=
      exists_mul_of_mem_inf_centralizer h113 h37 h38 h3228 hyp h2 hb ht htn hy
    have hvx := Subgroup.mem_centralizer_iff.mp hxV v hv
    have hcx := Subgroup.mem_centralizer_iff.mp hc.2 x hxL0
    calc v * c * x = v * (c * x) := by group
      _ = v * (x * c) := by rw [← hcx]
      _ = (v * x) * c := by group
      _ = (x * v) * c := by rw [hvx]
      _ = x * (v * c) := by group
  have hxT : x ∈ T := B6.pCoreOf_two_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right) hxO
  obtain ⟨k, hk⟩ := hyp.fsu.sylow.1 ⟨x, hxT⟩
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
    have := congrArg Subtype.val hk
    simpa using this)
  rw [hx3] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow hdvd)
  omega

end CFSG.Quasithin.Vol2.Ch10.SecF
