module

public import CFSG.Quasithin.H13.L32AL3i
public import CFSG.Quasithin.H13.L32AL2z
public import CFSG.Quasithin.H13.L32AL3c

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K (fsuV1 T V) t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]
  {F : Type} [Field F] [Finite F] [CharP F 2] (e : Hat V (A6.g1 T V) (fsuV1 T V) ≃* VM F)
  {t : ↥(A6.g1 T V)} {z z' : G} {hz'U : z' ∈ conjClosure V (A6.g1 T V)}

omit [Finite F] [CharP F 2] in
theorem mem_sup_img {n : ↥(A6.g1 T V)} (hn : (n : G) ∈ l1 T L V ⊔ T) :
    MulAut.congr e (X.top.act n) ∈ (X.img (l1 T L V)).map (MulAut.congr e).toMonoidHom ⊔
      (X.img T).map (MulAut.congr e).toMonoidHom := by
  have hL1H : l1 T L V ≤ A6.g1 T V := Setting147.l1H' X.R.S
  have hTH : T ≤ A6.g1 T V := Setting147.TH' X.R.S
  rw [← Subgroup.map_sup, img, img, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hL1H hTH]
  exact ⟨_, ⟨n, Subgroup.mem_subgroupOf.mpr hn, rfl⟩, rfl⟩

theorem le_normalizer_TY (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (hz : Subgroup.zpowers z = fsuV1 T V) (h : A114Hyp (fsuV1 T V ⊔ Subgroup.zpowers z') z z')
    (C : X.CfgAt e t hz'U) :
    l1 T L V ⊔ T ≤ Subgroup.normalizer ((pCoreOf 2 (l1 T L V ⊔ T) ⊓
      Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) :
        Subgroup G) : Set G) := by
  have hL1H : l1 T L V ≤ A6.g1 T V := Setting147.l1H' X.R.S
  have hTH : T ≤ A6.g1 T V := Setting147.TH' X.R.S
  have hsupH : l1 T L V ⊔ T ≤ A6.g1 T V := sup_le hL1H hTH
  have hRT : pCoreOf 2 (l1 T L V ⊔ T) ≤ T := Setting147.R1_le_T X.R.S
  have hRN : l1 T L V ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have key : ∀ n ∈ l1 T L V ⊔ T, ∀ r ∈ pCoreOf 2 (l1 T L V ⊔ T) ⊓
      Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G),
      n * r * n⁻¹ ∈ pCoreOf 2 (l1 T L V ⊔ T) ⊓
        Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) := by
    intro n hn r hr
    obtain ⟨hrR, hrN⟩ := Subgroup.mem_inf.mp hr
    have hnrR : n * r * n⁻¹ ∈ pCoreOf 2 (l1 T L V ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (hRN hn) r).mp hrR
    refine Subgroup.mem_inf.mpr ⟨hnrR, ?_⟩
    set n' : ↥(A6.g1 T V) := ⟨n, hsupH hn⟩
    set r' : ↥(A6.g1 T V) := ⟨r, hTH (hRT hrR)⟩
    have hfix := (mem_normalizer_iff_fix (X := X) (e := e) hF hz h hz'U r').mp hrN
    rw [show n * r * n⁻¹ = ((n' * r' * n'⁻¹ : ↥(A6.g1 T V)) : G) from rfl,
      mem_normalizer_iff_fix (X := X) (e := e) hF hz h hz'U]
    have hn' := mem_sup_img X e (n := n'⁻¹) (by
      show (n : G)⁻¹ ∈ l1 T L V ⊔ T
      exact Subgroup.inv_mem _ hn)
    have hr' : MulAut.congr e (X.top.act r') ∈
        (X.img (pCoreOf 2 (l1 T L V ⊔ T))).map (MulAut.congr e).toMonoidHom :=
      (mem_map_img_iff e).mpr ⟨r', hrR, rfl⟩
    have h2 := (C.fix_iff hn' hr').mpr hfix
    simp only [map_mul, map_inv, MulAut.mul_apply]
    simp only [map_inv] at h2
    rw [h2, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨key n hn r, fun h' => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ h'
  simpa [mul_assoc] using this

omit [Finite F] [CharP F 2] in
theorem mem_R1_of_img (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {x : ↥(A6.g1 T V)}
    (hx : MulAut.congr e (X.top.act x) ∈
      (X.img (pCoreOf 2 (l1 T L V ⊔ T))).map (MulAut.congr e).toMonoidHom) :
    (x : G) ∈ pCoreOf 2 (l1 T L V ⊔ T) := by
  obtain ⟨r, hrR, hr⟩ := (mem_map_img_iff e).mp hx
  have h1 : X.top.act (r⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, inv_mul_eq_one]
    exact (MulAut.congr e).injective hr
  rw [X.act_eq_one_iff hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334] at h1
  have h2 := (pCoreOf 2 (l1 T L V ⊔ T)).mul_mem hrR (Setting147.O2H_le_R1 X.R.S h1)
  simpa using h2

omit [Finite F] [CharP F 2] [IsMulCommutative ↥(conjClosure V (A6.g1 T V))] in
include X in
theorem pCoreOf_g1_le_TY (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (hz : Subgroup.zpowers z = fsuV1 T V) (h : A114Hyp (fsuV1 T V ⊔ Subgroup.zpowers z') z z')
    (hz'U : z' ∈ conjClosure V (A6.g1 T V)) :
    pCoreOf 2 (A6.g1 T V) ≤ pCoreOf 2 (l1 T L V ⊔ T) ⊓
      Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) := by
  intro q hq
  have hqG : q ∈ A6.g1 T V := pCoreOf_le 2 _ hq
  have hqz : q * z * q⁻¹ = z := by
    have hqC : q ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [centralizer_singleton_eq hF hz]
      exact hqG
    rw [Subgroup.mem_centralizer_singleton_iff.mp hqC, mul_inv_cancel_right]
  have hq' := hq
  rw [hF.toHypF91.pCoreOf_eq_centralizerMod] at hq'
  exact ⟨Setting147.O2H_le_R1 X.R.S hq,
    (mem_normalizer_sup_iff hz h hqG hqz).mpr ((mem_centralizerMod.mp hq').2.2 z' hz'U)⟩

omit [Finite F] [CharP F 2] [IsMulCommutative ↥(conjClosure V (A6.g1 T V))] in
include X in
theorem V_le_TY (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V)) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (hz'U : z' ∈ conjClosure V (A6.g1 T V)) :
    V ≤ pCoreOf 2 (l1 T L V ⊔ T) ⊓
      Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) := by
  have S := X.R.S
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨hVel, -, hLTV, -, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  have : IsMulCommutative ↥V := hVel.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  have hL1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hVR : V ≤ pCoreOf 2 (l1 T L V ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (S14.VT.trans le_sup_right)
      ((sup_le_sup_right hL1L T).trans hLTV) (F7.isPGroup_of_isElemAbelian hVel)
  refine le_inf hVR fun v hv => ?_
  have hUe := hF.F911_3
  have hVYU : fsuV1 T V ⊔ Subgroup.zpowers z' ≤ conjClosure V (A6.g1 T V) :=
    sup_le (hF.toHypF91.V₁_le_V.trans (le_conjClosure V _)) (Subgroup.zpowers_le.mpr hz'U)
  have hvU : v ∈ conjClosure V (A6.g1 T V) := le_conjClosure V _ hv
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have hcomm : ∀ w ∈ conjClosure V (A6.g1 T V), v * w * v⁻¹ = w := fun w hw => by
    rw [F7.isElemAbelian_comm hUe hvU hw, mul_inv_cancel_right]
  constructor
  · intro hw
    rw [hcomm w (hVYU hw)]
    exact hw
  · intro hw
    have hwU : w ∈ conjClosure V (A6.g1 T V) := by
      have h2 := hVYU hw
      rw [hcomm w ?_] at h2
      · exact h2
      · have h3 : v⁻¹ * (v * w * v⁻¹) * v = w := by group
        rw [← h3]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hvU) h2) hvU
    rw [hcomm w hwU] at hw
    exact hw

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
