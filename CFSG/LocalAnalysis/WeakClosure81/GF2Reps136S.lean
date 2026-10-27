module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Defs
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem w1369_commSub_top_map_conj (L : Subgroup (MulAut W)) (g : MulAut W) :
    commSub ⊤ (L.map (MulAut.conj g).toMonoidHom) = (commSub ⊤ L).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, -, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    refine ⟨x₀ (g⁻¹ w) * (g⁻¹ w)⁻¹, ⟨x₀, hx₀, g⁻¹ w, trivial, rfl⟩, ?_⟩
    change g (x₀ (g⁻¹ w) * (g⁻¹ w)⁻¹) = (MulAut.conj g x₀) w * w⁻¹
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.apply_inv_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, v, -, rfl⟩ := hs
    refine ⟨MulAut.conj g x₀, ⟨x₀, hx₀, rfl⟩, g v, trivial, ?_⟩
    change (MulAut.conj g x₀) (g v) * (g v)⁻¹ = g (x₀ v * v⁻¹)
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.inv_apply_self,
      map_mul, map_inv]

theorem lemmaS {A L : Subgroup (MulAut W)} (hLA : L ≤ A)
    (h : commSub ⊤ (⨆ φ ∈ A, L.map (MulAut.conj φ).toMonoidHom) = ⊤) :
    (⨆ X ∈ conjSubs A (commSub ⊤ L), X) = ⊤ := by
  classical
  let H : Subgroup (MulAut W) := ⨆ φ ∈ A, L.map (MulAut.conj φ).toMonoidHom
  let S : Subgroup W := ⨆ X ∈ conjSubs A (commSub ⊤ L), X
  have hS : S = ⨆ X : {X : Subgroup W // X ∈ conjSubs A (commSub ⊤ L)}, (X : Subgroup W) :=
    (iSup_subtype'' (conjSubs A (commSub ⊤ L)) fun X => X).symm
  have hstabA : StableUnder A S := by
    have hmap : ∀ a ∈ A, S.map a.toMonoidHom ≤ S := by
      intro a ha
      rw [hS, Subgroup.map_iSup]
      refine iSup_le fun X => ?_
      obtain ⟨φ, hφA, hXeq⟩ := X.2
      rw [hXeq, Subgroup.map_map]
      rw [show a.toMonoidHom.comp φ.toMonoidHom = (a * φ).toMonoidHom from rfl]
      exact le_iSup_of_le (⟨(commSub ⊤ L).map (a * φ).toMonoidHom,
        ⟨a * φ, A.mul_mem ha hφA, rfl⟩⟩ :
          {X : Subgroup W // X ∈ conjSubs A (commSub ⊤ L)}) le_rfl
    intro a ha s hs
    exact hmap a ha (Subgroup.mem_map_of_mem a.toMonoidHom hs)
  have hHA : H ≤ A := by
    refine iSup₂_le fun φ hφ => ?_
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    show (MulAut.conj φ) l ∈ A
    rw [MulAut.conj_apply]
    exact A.mul_mem (A.mul_mem hφ (hLA hl)) (A.inv_mem hφ)
  have hstabH : StableUnder H S := fun h hh => hstabA h (hHA hh)
  let T : Subgroup (MulAut W) :=
    { carrier := {x | x ∈ H ∧ ∀ w : W, x w * w⁻¹ ∈ S}
      one_mem' := ⟨H.one_mem, fun w => by
        rw [show (1 : MulAut W) w = w from rfl, mul_inv_cancel]
        exact S.one_mem⟩
      mul_mem' := by
        rintro x y ⟨hxH, hx⟩ ⟨hyH, hy⟩
        refine ⟨H.mul_mem hxH hyH, fun w => ?_⟩
        have h1 : x (y w * w⁻¹) ∈ S := hstabH x hxH _ (hy w)
        have h2 : x w * w⁻¹ ∈ S := hx w
        have heq : (x * y) w * w⁻¹ = x (y w * w⁻¹) * (x w * w⁻¹) := by
          simp only [MulAut.mul_apply, map_mul, map_inv]
          group
        rw [heq]
        exact S.mul_mem h1 h2
      inv_mem' := by
        rintro x ⟨hxH, hx⟩
        refine ⟨H.inv_mem hxH, fun w => ?_⟩
        have hmem : (x (x⁻¹ w) * (x⁻¹ w)⁻¹)⁻¹ ∈ S := S.inv_mem (hx (x⁻¹ w))
        have heq : (x (x⁻¹ w) * (x⁻¹ w)⁻¹)⁻¹ = x⁻¹ w * w⁻¹ := by
          rw [show x (x⁻¹ w) = w from by simp]
          group
        rwa [heq] at hmem }
  have hLmemT : ∀ φ ∈ A, L.map (MulAut.conj φ).toMonoidHom ≤ T := by
    intro φ hφ x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨?_, ?_⟩
    · show (MulAut.conj φ) l ∈ H
      exact Subgroup.mem_iSup_of_mem φ (Subgroup.mem_iSup_of_mem hφ
        (Subgroup.mem_map_of_mem (MulAut.conj φ).toMonoidHom hl))
    · intro w
      have hmem : ((MulAut.conj φ).toMonoidHom l) w * w⁻¹ ∈
          commSub ⊤ (L.map (MulAut.conj φ).toMonoidHom) :=
        Subgroup.subset_closure ⟨(MulAut.conj φ).toMonoidHom l,
          Subgroup.mem_map_of_mem _ hl, w, trivial, rfl⟩
      rw [w1369_commSub_top_map_conj L φ] at hmem
      rw [hS]
      exact Subgroup.mem_iSup_of_mem (⟨(commSub ⊤ L).map φ.toMonoidHom,
        ⟨φ, hφ, rfl⟩⟩ : {X : Subgroup W // X ∈ conjSubs A (commSub ⊤ L)}) hmem
  have hHT : H ≤ T := iSup₂_le hLmemT
  have hle : commSub ⊤ H ≤ S := by
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, -, rfl⟩
    exact (hHT hx).2 w
  change S = ⊤
  exact eq_top_iff.mpr (h ▸ hle)

theorem comm_top_of_odd {Y : Subgroup (MulAut W)} {t : MulAut W} (S : Std136 Y t)
    (hw2 : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)} (hHY : H ≤ Y)
    (hH : (H.subgroupOf Y).Normal) (hodd : Odd (Nat.card H)) (hH1 : H ≠ ⊥) :
    commSub ⊤ H = ⊤ := by
  obtain ⟨hsup, -⟩ := coprime_decomp (P := H) hodd hw2 (W := (⊤ : Subgroup W))
    (fun _ _ _ _ => Subgroup.mem_top _)
  have hn : ∀ y ∈ Y, ∀ h ∈ H, y * h * y⁻¹ ∈ H :=
    fun y hy h hh => (Subgroup.normal_subgroupOf_iff hHY).mp hH h y hh hy
  have hstabC : StableUnder Y (commSub ⊤ H) := by
    intro y hy c hc
    refine Subgroup.closure_induction (p := fun c _ => y c ∈ commSub ⊤ H) ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨h, hh, w, -, rfl⟩
      refine Subgroup.subset_closure ⟨y * h * y⁻¹, hn y hy h hh, y w, trivial, ?_⟩
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, ← map_inv, map_mul]
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro a b _ _ ha hb
      rw [map_mul]
      exact (commSub ⊤ H).mul_mem ha hb
    · intro a _ ha
      rw [map_inv]
      exact (commSub ⊤ H).inv_mem ha
  have hstabF : StableUnder Y (fixV H) := by
    intro y hy v hv
    rw [mem_fixV] at hv ⊢
    intro h hh
    have hmem : y⁻¹ * h * y ∈ H := hn y⁻¹ (Y.inv_mem hy) h hh
    have hfix : (y⁻¹ * h * y) v = v := hv _ hmem
    have h1 : y⁻¹ (h (y v)) = v := by
      rw [MulAut.mul_apply, MulAut.mul_apply] at hfix
      exact hfix
    calc h (y v) = y (y⁻¹ (h (y v))) := (MulEquiv.apply_symm_apply y _).symm
      _ = y v := by rw [h1]
  have htop : commSub ⊤ H ⊔ fixV H = ⊤ := by simpa using hsup
  rcases S.basic.1 (commSub ⊤ H) (fixV H) hstabC hstabF htop with hC | hF
  · exact hC
  · exfalso
    apply hH1
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    ext w
    exact (mem_fixV.mp (by rw [hF]; exact Subgroup.mem_top w)) a ha

theorem comm_top_of_component {Y : Subgroup (MulAut W)} {t : MulAut W} (S : Std136 Y t)
    (hw2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hL : IsComponentOf L Y) :
    commSub ⊤ (⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom) = ⊤ := by
  classical
  let H : Subgroup (MulAut W) := ⨆ φ ∈ Y, L.map (MulAut.conj φ).toMonoidHom
  have hLY : L ≤ Y := hL.1
  have hHY : H ≤ Y := by
    refine iSup₂_le fun φ hφ => ?_
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    show (MulAut.conj φ) l ∈ Y
    rw [MulAut.conj_apply]
    exact Y.mul_mem (Y.mul_mem hφ (hLY hl)) (Y.inv_mem hφ)
  have hHn : (H.subgroupOf Y).Normal := by
    let Hsub : Subgroup (MulAut W) :=
      ⨆ φ : Y, L.map (MulAut.conj (φ : MulAut W)).toMonoidHom
    have hHsub : H = Hsub :=
      (iSup_subtype'' (Y : Set (MulAut W)) fun φ => L.map (MulAut.conj φ).toMonoidHom).symm
    rw [Subgroup.normal_subgroupOf_iff hHY]
    intro h k hh hk
    rw [hHsub] at hh ⊢
    refine Subgroup.iSup_induction (C := fun x => k * x * k⁻¹ ∈ Hsub)
      (fun φ : Y => L.map (MulAut.conj (φ : MulAut W)).toMonoidHom) hh ?_ ?_ ?_
    · intro φ z hz
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_iSup_of_mem (⟨k * (φ : MulAut W), Y.mul_mem hk φ.2⟩ : Y) ?_
      refine Subgroup.mem_map.mpr ⟨l, hl, ?_⟩
      show (MulAut.conj (k * (φ : MulAut W))).toMonoidHom l =
        k * (MulAut.conj (φ : MulAut W)).toMonoidHom l * k⁻¹
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · intro x z hx hz
      have heq : k * (x * z) * k⁻¹ = (k * x * k⁻¹) * (k * z * k⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ hx hz
  have hLne : L ≠ ⊥ := by
    rw [← Subgroup.nontrivial_iff_ne_bot]
    haveI := hL.2.2.2
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (congrArg QuotientGroup.mk h)⟩
  have hHne : H ≠ ⊥ := by
    intro hbot
    apply hLne
    have hLH : L ≤ H := by
      have h1 : L.map (MulAut.conj (1 : MulAut W)).toMonoidHom = L := by
        ext x
        simp [MulAut.conj]
      rw [← h1]
      exact le_iSup₂_of_le (1 : MulAut W) Y.one_mem le_rfl
    rw [hbot] at hLH
    exact le_bot_iff.mp hLH
  have h125 := w4Lem12_5_holds W hw2 Y S.o2 S.basic H hHne hHY hHn
  have hspan : (⨆ I ∈ irrSet H, I) = ⊤ := ((h125.2 L hL rfl).1).1
  have hle : (⨆ I ∈ irrSet H, I) ≤ commSub ⊤ H := by
    refine iSup₂_le fun I hI => ?_
    rw [← hI.1]
    exact commSub_mono le_top le_rfl
  rw [hspan] at hle
  change commSub ⊤ H = ⊤
  exact eq_top_iff.mpr hle

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
