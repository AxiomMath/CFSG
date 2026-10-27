module

public import CFSG.Quasithin.H13.L32AL3j
public import CFSG.Quasithin.H13.L32AL3e

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G} {t₀ : G}

omit [Finite G] in
theorem centralizer_sup_le (z' : G) :
    Subgroup.centralizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) ≤
      A6.g1 T V := fun x hx =>
  Subgroup.centralizer_le_normalizer _
    (Subgroup.centralizer_le (le_sup_left : fsuV1 T V ≤ _) hx)

namespace TopCtx

variable (X : TopCtx T L V K (fsuV1 T V) t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]
  {F : Type} [Field F] [Finite F] [CharP F 2] (e : Hat V (A6.g1 T V) (fsuV1 T V) ≃* VM F)
  {t : ↥(A6.g1 T V)} {z z' : G} {hz'U : z' ∈ conjClosure V (A6.g1 T V)}

theorem pCoreOf_le_TY (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (hz : Subgroup.zpowers z = fsuV1 T V) (h : A114Hyp (fsuV1 T V ⊔ Subgroup.zpowers z') z z')
    (C : X.CfgAt e t hz'U)
    (he1 : (X.img (conjClosure K T)).map (MulAut.congr e).toMonoidHom = (rho (K := F)).range)
    (htR : (t : G) ∈ pCoreOf 2 (l1 T L V ⊔ T)) :
    pCoreOf 2 (a114Y z z') ≤ pCoreOf 2 (l1 T L V ⊔ T) ⊓
      Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) := by
  obtain ⟨-, -, hker, -⟩ := a114_one h
  obtain ⟨-, -, hNY⟩ := a114_two h
  have hOC : pCoreOf 2 (a114Y z z') ≤
      Subgroup.centralizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) := by
    rw [← hker]
    exact inf_le_right
  have hOG : pCoreOf 2 (a114Y z z') ≤ A6.g1 T V := hOC.trans (centralizer_sup_le z')
  have hON : pCoreOf 2 (a114Y z z') ≤
      Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) :=
    hOC.trans (Subgroup.centralizer_le_normalizer _)
  set N := (X.img (pCoreOf 2 (a114Y z z'))).map (MulAut.congr e).toMonoidHom with hN
  have hNH : N ≤ (X.img (A6.g1 T V)).map (MulAut.congr e).toMonoidHom :=
    Subgroup.map_mono (X.img_mono hOG)
  have hN2 : ∀ x ∈ N, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨k, hk⟩ := exists_pow_of_mem_map X.top.act (pCoreOf_isPGroup 2 (a114Y z z')) hf
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  have hNa : ∀ x ∈ N, x (e (InternalSec.secMk ((fsuV1 T V).subgroupOf
      (conjClosure V (A6.g1 T V))) ⟨z', hz'U⟩)) = e (InternalSec.secMk ((fsuV1 T V).subgroupOf
      (conjClosure V (A6.g1 T V))) ⟨z', hz'U⟩) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_map_img_iff e).mp hx
    exact (mem_normalizer_iff_fix (X := X) (e := e) hF hz h hz'U y).mp (hON hy)
  have hDN : ∀ d ∈ (rho (K := F)).range, d (e (InternalSec.secMk ((fsuV1 T V).subgroupOf
      (conjClosure V (A6.g1 T V))) ⟨z', hz'U⟩)) = e (InternalSec.secMk ((fsuV1 T V).subgroupOf
      (conjClosure V (A6.g1 T V))) ⟨z', hz'U⟩) →
      d ∈ Subgroup.normalizer (N : Set (MulAut (VM F))) := by
    intro d hd hda
    rw [← he1] at hd
    obtain ⟨k, -, rfl⟩ := (mem_map_img_iff e).mp hd
    have hkV := (mem_normalizer_iff_fix (X := X) (e := e) hF hz h hz'U k).mpr hda
    have hkO : (k : G) ∈ Subgroup.normalizer (pCoreOf 2 (a114Y z z') : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 _ (hNY hkV)
    have h1 := map_subgroupOf_le_normalizer X.top.act
      (le_refl (Subgroup.normalizer (pCoreOf 2 (a114Y z z') : Set G)))
    have h2 : X.top.act k ∈ Subgroup.normalizer (X.img (pCoreOf 2 (a114Y z z')) :
        Set (MulAut (Hat V (A6.g1 T V) (fsuV1 T V)))) :=
      h1 ⟨k, Subgroup.mem_subgroupOf.mpr hkO, rfl⟩
    exact Subgroup.le_normalizer_map _ ⟨_, h2, rfl⟩
  have hle := C.le_zpowers hNH hN2 hNa hDN
  intro y hy
  refine ⟨?_, hON hy⟩
  set y' : ↥(A6.g1 T V) := ⟨y, hOG hy⟩
  have hyN : MulAut.congr e (X.top.act y') ∈ N := (mem_map_img_iff e).mpr ⟨y', hy, rfl⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hle hyN)
  refine X.mem_R1_of_img e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 (x := y') ?_
  rw [← hm]
  exact Subgroup.zpow_mem _ ((mem_map_img_iff e).mpr ⟨t, htR, rfl⟩) m

theorem sZero_le_img (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (C : X.CfgAt e t hz'U) :
    (sZero : Subgroup (MulAut (VM F))) ≤
      (X.img (pCoreOf 2 (l1 T L V))).map (MulAut.congr e).toMonoidHom :=
  X.le_map_img_pCore e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 C.sZero_le
    C.ls_le_normalizer_sZero fun x hx => ⟨1, by rw [pow_one, pow_two, sZero_sq hx]⟩

theorem not_le_normalizer (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V))
    (hz : Subgroup.zpowers z = fsuV1 T V) (h : A114Hyp (fsuV1 T V ⊔ Subgroup.zpowers z') z z')
    (C : X.CfgAt e t hz'U) :
    ¬ pCoreOf 2 (l1 T L V) ≤
      Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) := by
  intro hle
  obtain ⟨s, hs, hsa⟩ := C.exists_sZero_move
  obtain ⟨l, hlO, rfl⟩ := (mem_map_img_iff e).mp
    (X.sZero_le_img e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 C hs)
  exact hsa ((mem_normalizer_iff_fix (X := X) (e := e) hF hz h hz'U l).mp (hle hlO))

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
