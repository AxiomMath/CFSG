module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionNormal

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis CFSG.QuasithinUnique.Fin257

section Aux

variable {G : Type} [Group G]

theorem sixFF_ff6_aux_diagTorus_dSp {K : Type} [Field K] [CharP K 2] {j : antiSp K}
    (hj : j ∈ GomiFusion.diagTorus K) : ∃ r s : Kˣ, j = Sp4.dSp r s := by
  obtain ⟨r, s, hr, hs, hg⟩ := hj
  refine ⟨Units.mk0 r⁻¹ (inv_ne_zero hr), Units.mk0 s⁻¹ (inv_ne_zero hs), mat_ext ?_⟩
  show glMat (j : GL (Fin 4) K) = glMat ((Sp4.dSp _ _ : antiSp K) : GL (Fin 4) K)
  rw [hg, Sp4.glMat_dSp]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [GomiFusion.diagMat, Sp4.dSpMat, Matrix.diagonal]

theorem sixFF_ff6_aux_mem_normalizer_zpowers {t g : G}
    (hC : g ∈ Subgroup.centralizer ({t} : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  have ht : g * t * g⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hC, mul_inv_cancel_right]
  have ht' : g⁻¹ * t * g = t := by
    have hC' := Subgroup.mem_centralizer_singleton_iff.1 (inv_mem hC)
    rw [hC', mul_assoc, inv_mul_cancel, mul_one]
  have hz : ∀ h : G, h * t * h⁻¹ = t → ∀ x ∈ Subgroup.zpowers t,
      h * x * h⁻¹ ∈ Subgroup.zpowers t := by
    intro h hh x hx
    have hle : Subgroup.zpowers t ≤ (Subgroup.zpowers t).comap (MulAut.conj h).toMonoidHom :=
      Subgroup.zpowers_le.2 (by
        show h * t * h⁻¹ ∈ Subgroup.zpowers t
        rw [hh]; exact Subgroup.mem_zpowers t)
    exact hle hx
  refine FieldInvolution.mem_normalizer_of_conj_mem_of_inv (hz g ht) fun x hx => ?_
  have := hz g⁻¹ (by rw [inv_inv]; exact ht') x hx
  rwa [inv_inv] at this

theorem sixFF_ff6_aux_normalizer_sup_zpowers {A : Subgroup G} {t g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hC : g ∈ Subgroup.centralizer ({t} : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ Subgroup.zpowers t : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_sup _ _
    (Subgroup.mem_inf.mpr ⟨hA, sixFF_ff6_aux_mem_normalizer_zpowers hC⟩)

end Aux

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff6 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hK : SixKConclusion φ t i) (f1 : FF1Concl φ t i) (f2 : FF2Concl n φ t i)
    (f3 : FF3Concl φ t i) : FF6Concl n φ t i := by
  intro u hu1 hu2 hu3
  have hsu := hS.fc.setup
  have hn : 2 ≤ n := hsu.two_le
  have hn1 : 1 ≤ n := by omega
  have hK' : Nat.card K = 2 ^ n := hsu.card_K
  have hLC : L ≤ Subgroup.centralizer ({t} : Set G) := hsu.L_le
  have hCN : ∀ y ∈ Subgroup.centralizer ({t} : Set G), y ∈ Subgroup.normalizer (L : Set G) :=
    fun y hy => hsu.cent_le hy
  have hVP : S φ t i ⊓ Subgroup.centralizer ({t} : Set G) = P φ := hK.centralizer_S
  have hPVC : ∀ x, x ∈ P φ ↔ x ∈ S φ t i ∧ x ∈ Subgroup.centralizer ({t} : Set G) :=
    fun x => by rw [← Subgroup.mem_inf, hVP]
  have hVT : S φ t i ≤ Tplus φ t i := by
    rw [← hH.sup_t]; exact le_sup_left
  have htT : t ∈ Tplus φ t i := by
    rw [← hH.sup_t]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hNT : ∀ g : G, g ∈ Subgroup.centralizer ({t} : Set G) →
      g ∈ Subgroup.normalizer (S φ t i : Set G) →
      g ∈ Subgroup.normalizer (Tplus φ t i : Set G) := by
    intro g hg hgS
    rw [← hH.sup_t]
    exact sixFF_ff6_aux_normalizer_sup_zpowers hgS hg
  have hCL : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (L : Set G) =
      Subgroup.zpowers t := by
    rw [inf_comm]; exact hsu.cent_inf
  obtain ⟨a, haV, hta⟩ : ∃ a ∈ S φ t i, u⁻¹ * t * u = a⁻¹ * t * a :=
    hK.slice u ((Subgroup.mem_normalizer_iff''.1 hu1 t).1 htT)
  set h := u * a⁻¹ with hhdef
  have hhC : h ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : t * u = u * (a⁻¹ * t * a) := by rw [← hta]; group
    calc u * a⁻¹ * t = u * (a⁻¹ * t * a) * a⁻¹ := by group
      _ = t * u * a⁻¹ := by rw [← e]
      _ = t * (u * a⁻¹) := by group
  have hhN := hCN h hhC
  have haN : a ∈ Subgroup.normalizer (S φ t i : Set G) := Subgroup.le_normalizer haV
  have hNu : u ∈ Subgroup.normalizer (S φ t i : Set G) := f3 hu1
  have hhT : h ∈ Subgroup.normalizer (Tplus φ t i : Set G) :=
    mul_mem hu1 (inv_mem (Subgroup.le_normalizer (hVT haV)))
  have hhV : h ∈ Subgroup.normalizer (S φ t i : Set G) := mul_mem hNu (inv_mem haN)
  obtain ⟨hhP, hhUi, hhUj⟩ := f1 h hhT hhC
  obtain ⟨p', hp'U, j, hjD, k, hk, hαh'⟩ := f2 ⟨h, hhN⟩ hhC hhP hhUi hhUj
  obtain ⟨r, s, rfl⟩ := sixFF_ff6_aux_diagTorus_dSp hjD
  set α := FieldInvolution.transAct (G := G) φ with hαdef
  obtain ⟨p, hpdef⟩ : ∃ p : G, p = ((φ.symm p' : L) : G) := ⟨_, rfl⟩
  have hpL : p ∈ L := by rw [hpdef]; exact (φ.symm p').2
  have hpP : p ∈ P φ := by rw [hpdef]; exact symm_mem_pull.2 hp'U
  obtain ⟨hpV, hpC⟩ := (hPVC p).1 hpP
  have hpN : p ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hpL
  have hαp : α ⟨p, hpN⟩ = MulAut.conj p' := by
    rw [FieldInvolution.transAct_of_mem φ ⟨p, hpN⟩ hpL]
    have e : (⟨p, hpL⟩ : L) = φ.symm p' := Subtype.ext hpdef
    rw [e, MulEquiv.apply_symm_apply]
  set v := p⁻¹ * h with hvdef
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem hpN) hhN
  have hαv : α ⟨v, hvN⟩ = MulAut.conj (Sp4.dSp r s) * frobAut K ^ k := by
    have e : (⟨v, hvN⟩ : Subgroup.normalizer (L : Set G)) = ⟨p, hpN⟩⁻¹ * ⟨h, hhN⟩ := rfl
    rw [e, map_mul, map_inv, hαp, hαh', map_mul]
    group
  have huv : u⁻¹ * v ∈ S φ t i := by
    rw [show u⁻¹ * v = u⁻¹ * p⁻¹ * u * a⁻¹ by rw [hvdef, hhdef]; group]
    exact (S φ t i).mul_mem ((Subgroup.mem_normalizer_iff''.1 hNu _).1
      ((S φ t i).inv_mem hpV)) ((S φ t i).inv_mem haV)
  have hvT : v ∈ Subgroup.normalizer (Tplus φ t i : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer (hVT hpV))) hhT
  have hvV : v ∈ Subgroup.normalizer (S φ t i : Set G) := f3 hvT
  have hvC : v ∈ Subgroup.centralizer ({t} : Set G) := mul_mem (inv_mem hpC) hhC
  have hu2V : u ^ 2 ∈ S φ t i := by rw [pow_two]; exact hu3
  have hv2V : v ^ 2 ∈ S φ t i := by
    rw [pow_two, show v * v = u ^ 2 * (u⁻¹ * (u⁻¹ * v) * u) * (u⁻¹ * v) by group]
    exact (S φ t i).mul_mem ((S φ t i).mul_mem hu2V
      ((Subgroup.mem_normalizer_iff''.1 hNu _).1 huv)) huv
  have hv2P : v ^ 2 ∈ P φ := (hPVC _).2 ⟨hv2V, pow_mem hvC 2⟩
  obtain ⟨hv2L, hyU⟩ := mem_pull.1 hv2P
  have hαv2 : MulAut.conj (φ ⟨v ^ 2, hv2L⟩) = (MulAut.conj (Sp4.dSp r s) * frobAut K ^ k) ^ 2 := by
    have e : (⟨v, hvN⟩ : Subgroup.normalizer (L : Set G)) ^ 2 = ⟨v ^ 2, pow_mem hvN 2⟩ :=
      Subtype.ext (Subgroup.coe_pow _ _ 2)
    rw [← hαv, ← map_pow, e, FieldInvolution.transAct_of_mem φ _ hv2L]
  obtain ⟨hy1, hjj, hkn⟩ := FieldInvolution.eq_one_of_conj_eq_sq hn1 hK' hk hyU hαv2
  have hv2 : v * v = 1 := by
    have h1 : (⟨v ^ 2, hv2L⟩ : L) = 1 := φ.injective (by rw [hy1, map_one])
    have h2 : v ^ 2 = 1 := congrArg Subtype.val h1
    rwa [pow_two] at h2
  have huT' : ∀ w, u⁻¹ * w ∈ S φ t i → w ∈ Tplus φ t i → False := by
    intro w hw hwT
    apply hu2
    have h1 : u⁻¹ * w * w⁻¹ ∈ Tplus φ t i := mul_mem (hVT hw) (inv_mem hwT)
    rw [mul_inv_cancel_right] at h1
    have h2 := inv_mem h1
    rwa [inv_inv] at h2
  have hzT : Subgroup.zpowers t ≤ Tplus φ t i := by
    rw [← hH.sup_t]; exact le_sup_right
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, MulAut.one_apply] at hjj
    have hj1 : Sp4.dSp r s = 1 := FieldInvolution.dSp_eq_one_of_mul_self hjj
    have hα1 : α ⟨v, hvN⟩ = 1 := by rw [hαv, hj1, map_one, pow_zero, mul_one]
    have hvt : v ∈ Subgroup.zpowers t := by
      rw [← hCL]
      exact ⟨hvC, (FieldInvolution.transAct_eq_one_iff φ ⟨v, hvN⟩).1 hα1⟩
    exact huT' v huv (hzT hvt)
  have hnk : n = 2 * k := hkn.resolve_left hk0
  have hn2 : n / 2 = k := by omega
  obtain ⟨b, c, hjbc⟩ := FieldInvolution.exists_dSp_eq_mul_frob_inv (m := k) (by omega)
    (by rw [hK', hnk]) hjj
  set d : G := ((φ.symm (Sp4.dSp b c) : L) : G) with hddef
  have hdL : d ∈ L := (φ.symm (Sp4.dSp b c)).2
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hdC : d ∈ Subgroup.centralizer ({t} : Set G) := hLC hdL
  have hαd : α ⟨d, hdN⟩ = MulAut.conj (Sp4.dSp b c) := by
    rw [FieldInvolution.transAct_of_mem φ _ hdL]
    have e' : (⟨d, hdL⟩ : L) = φ.symm (Sp4.dSp b c) := rfl
    rw [e', MulEquiv.apply_symm_apply]
  have hdJ0 : d ∈ J₀ φ := symm_mem_pull.2 (sixFF_ff2_aux_dSp_mem b c)
  have hJS : ∀ g ∈ J₀ φ, g ∈ Subgroup.normalizer (S φ t i : Set G) := by
    intro g hg
    obtain ⟨-, -, hJ1⟩ := hH.normal_Mhat Axis.one
    obtain ⟨-, -, hJ2⟩ := hH.normal_Mhat Axis.two
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr ⟨hJ1 hg, hJ2 hg⟩)
  have hdS : d ∈ Subgroup.normalizer (S φ t i : Set G) := hJS d hdJ0
  have hdT : d ∈ Subgroup.normalizer (Tplus φ t i : Set G) := hNT d hdC hdS
  set vd : G := d⁻¹ * v * d with hvddef
  have hvdN : vd ∈ Subgroup.normalizer (L : Set G) := mul_mem (mul_mem (inv_mem hdN) hvN) hdN
  have hαvd : α ⟨vd, hvdN⟩ = frobAut K ^ k := by
    have e' : (⟨vd, hvdN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨d, hdN⟩⁻¹ * ⟨v, hvN⟩ * ⟨d, hdN⟩ := rfl
    rw [e', map_mul, map_mul, map_inv, hαd, hαv]
    exact FieldInvolution.conj_inv_mul_conj_mul_conj _ (Sp4.dSp b c) (Sp4.dSp r s) hjbc
  have hfrob : ∀ l : L, ((φ.symm ((frobAut K ^ (n / 2)) (φ l)) : L) : G) = vd * l * vd⁻¹ := by
    intro l
    have h1 := FieldInvolution.coe_symm_transAct φ ⟨vd, hvdN⟩ (φ l)
    rw [hαvd, MulEquiv.symm_apply_apply] at h1
    rw [hn2]
    exact h1
  have hnotLC : ∀ w (hw : w ∈ Subgroup.normalizer (L : Set G)),
      (∀ g : antiSp K, α ⟨w, hw⟩ ≠ MulAut.conj g) →
      ¬ ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set G), w = l * c := by
    rintro w hw hne ⟨l, hl, c, hc, rfl⟩
    have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
    have hcN : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _ hc
    have e' : (⟨l * c, hw⟩ : Subgroup.normalizer (L : Set G)) = ⟨l, hlN⟩ * ⟨c, hcN⟩ := rfl
    apply hne (φ ⟨l, hl⟩)
    rw [e', map_mul, FieldInvolution.transAct_of_mem φ _ hl,
      (FieldInvolution.transAct_eq_one_iff φ ⟨c, hcN⟩).2 hc, mul_one]
  have hvdcoset : (d⁻¹ * u * d)⁻¹ * (d⁻¹ * v * d) ∈ S φ t i := by
    rw [show (d⁻¹ * u * d)⁻¹ * (d⁻¹ * v * d) = d⁻¹ * (u⁻¹ * v) * d by group]
    exact (Subgroup.mem_normalizer_iff''.1 hdS _).1 huv
  refine ⟨⟨k, by omega⟩, v, d, huv, hvC, hv2, ?_, hdJ0, hfrob, ?_, hvdcoset⟩
  · intro hv1
    exact huT' 1 (by rw [← hv1]; exact huv) (Tplus φ t i).one_mem
  · rintro w (rfl | rfl)
    · refine ⟨hvV, hvT, hvC, hnotLC _ hvN fun g => ?_⟩
      rw [hαv]
      exact FieldInvolution.conj_mul_frobAut_pow_ne_conj hn1 hK' hk0 hk (Sp4.dSp r s) g
    · refine ⟨mul_mem (mul_mem (inv_mem hdS) hvV) hdS, mul_mem (mul_mem (inv_mem hdT) hvT) hdT,
        mul_mem (mul_mem (inv_mem hdC) hvC) hdC, hnotLC _ hvdN fun g => ?_⟩
      rw [hαvd]
      have := FieldInvolution.conj_mul_frobAut_pow_ne_conj hn1 hK' hk0 hk 1 g
      rwa [map_one, one_mul] at this

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
