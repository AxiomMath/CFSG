module

public import CFSG.Quasithin.Background.RonanD321End

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391
  CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem map_mem_commV_of_normalizer {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) {u : W} (hu : u ∈ commV L) :
    g u ∈ commV L := by
  have h1 : g u ∈ (commV L).map g.toMonoidHom := ⟨u, hu, rfl⟩
  rwa [map_commV_conjAutSub, mem_normalizer_iff_conjAutSub.1 hg] at h1

theorem exists_irrPlus_of_fixed (hB : D321Base M Mp T L V t) (h3 : D321Three Mp L)
    {J : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))}
    (hJ : letI := qAct hB.hD.hyp.Mp_normal; XMod.IsIrr ↥(L.subgroupOf M) J)
    (hJU : J ≤ tilde Mp ⊤ (commV L))
    (hJN : letI := qAct hB.hD.hyp.Mp_normal;
      ∀ g : ↥M, (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) → g • J = J) :
    ∃ I ∈ IrrPlus L (commV L), M ⊓ Subgroup.normalizer (L : Set (MulAut W)) ≤ stabSub I := by
  let _i := qAct hB.hD.hyp.Mp_normal
  set π := QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hπ
  set P := J.comap π ⊓ commV L
  set I := commSub P L with hI
  have hLM := hB.L_le
  have hker : ∀ w : W, π w = 1 ↔ w ∈ fixV Mp := by
    intro w
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
  have hJfix : ∀ q ∈ J, q ∈ XMod.fixed ↥(L.subgroupOf M) ⊤ → q = 1 := by
    intro q hq hfix
    have h1 : q ∈ tilde Mp ⊤ (commV L) ⊓ XMod.fixed ↥(L.subgroupOf M) ⊤ := ⟨hJU hq, hfix⟩
    rw [tildeU_inf_fixed_eq_bot hB h3] at h1
    exact h1
  have hJcomm : XMod.commOf ↥(L.subgroupOf M) J = J := by
    rcases hJ.2.2 _ (XMod.isInv_commOf J) bot_le (XMod.commOf_le_of_isInv hJ.1) with h | h
    · exfalso
      have hfixJ : J ≤ XMod.fixed ↥(L.subgroupOf M) ⊤ := XMod.commOf_eq_bot_iff.1 h
      exact hJ.2.1.ne' (eq_bot_iff.2 fun q hq => hJfix q hq (hfixJ hq))
    · exact h
  have hPinv : ∀ x ∈ L, ∀ p ∈ P, x p ∈ P := by
    intro x hx p hp
    refine ⟨?_, map_mem_commV_of_normalizer (Subgroup.le_normalizer hx) hp.2⟩
    show π (x p) ∈ J
    exact hJ.1 ⟨⟨x, hLM hx⟩, hx⟩ (π p) hp.1
  have hIP : I ≤ P := commSub_le_of_invariant hPinv
  have hIU : I ≤ commV L := hIP.trans inf_le_right
  have hIinv : ∀ x ∈ L, ∀ w ∈ I, x w ∈ I := by
    have h1 := XMod.isInv_commOf (A := ↥L) P
    rw [commOf_eq_commSub, isInv_iff] at h1
    exact h1
  have hπP : P.map π = J := by
    refine le_antisymm ?_ fun q hq => ?_
    · rintro _ ⟨p, hp, rfl⟩
      exact hp.1
    · obtain ⟨u, hu, rfl⟩ := hJU hq
      exact ⟨u, ⟨hq, hu⟩, rfl⟩
  have hπcomm : ∀ S : Subgroup W,
      (commSub S L).map π = XMod.commOf ↥(L.subgroupOf M) (S.map π) := by
    intro S
    unfold commSub XMod.commOf
    rw [MonoidHom.map_closure]
    congr 1
    ext c
    constructor
    · rintro ⟨_, ⟨x, hx, w, hw, rfl⟩, rfl⟩
      exact ⟨⟨⟨x, hLM hx⟩, hx⟩, π w, ⟨w, hw, rfl⟩, rfl⟩
    · rintro ⟨a, q, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨_, ⟨((a : ↥M) : MulAut W), Subgroup.mem_subgroupOf.1 a.2, w, hw, rfl⟩, rfl⟩
  have hπI : I.map π = J := by rw [hπcomm, hπP, hJcomm]
  have hMpL : fixV Mp ≤ fixV L := fixV_anti hB.L_le_Mp
  have hFix : I ⊓ fixV L ≤ fixV Mp := by
    rintro i ⟨hi, hil⟩
    rw [← hker]
    have hiJ : π i ∈ J := hπI ▸ Subgroup.mem_map_of_mem π hi
    refine hJfix _ hiJ ⟨trivial, fun a => ?_⟩
    show π (((a : ↥M) : MulAut W) i) = π i
    rw [(mem_fixV.1 hil) _ (Subgroup.mem_subgroupOf.1 a.2)]
  have hfixI : XMod.fixed ↥L I = I ⊓ fixV Mp := by
    rw [fixed_eq_inf_fixV]
    exact le_antisymm (le_inf inf_le_left hFix) (inf_le_inf_left _ hMpL)
  have hPle : P ≤ I ⊔ fixV Mp := by
    intro p hp
    have h1 : π p ∈ I.map π := by rw [hπI]; exact hp.1
    obtain ⟨i, hi, hip⟩ := h1
    have h2 : i⁻¹ * p ∈ fixV Mp := by
      rw [← hker, map_mul, map_inv, hip, inv_mul_cancel]
    have e : p = i * (i⁻¹ * p) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hi h2
  have hIcomm : commSub I L = I := by
    refine le_antisymm (commSub_le_of_invariant hIinv) ?_
    calc I = commSub P L := rfl
      _ ≤ commSub (I ⊔ fixV Mp) L := commSub_mono hPle le_rfl
      _ = commSub I L := commSub_sup_fixV hMpL
  have hIrrSec : XMod.IsIrrSec ↥L (XMod.fixed ↥L I) I := by
    rw [hfixI]
    refine ⟨lt_of_le_of_ne inf_le_left fun h => ?_, fun K hK hCK hKI => ?_⟩
    · apply hJ.2.1.ne'
      rw [← hπI, eq_bot_iff]
      rintro _ ⟨i, hi, rfl⟩
      have h1 : i ∈ I ⊓ fixV Mp := by rw [h]; exact hi
      exact (hker i).2 h1.2
    · have hKinv : XMod.IsInv ↥(L.subgroupOf M) (K.map π) := by
        rintro a _ ⟨k, hk, rfl⟩
        exact ⟨((a : ↥M) : MulAut W) k,
          (isInv_iff L K).1 hK _ (Subgroup.mem_subgroupOf.1 a.2) k hk, rfl⟩
      have hKJ : K.map π ≤ J := hπI ▸ Subgroup.map_mono hKI
      rcases hJ.2.2 _ hKinv bot_le hKJ with h | h
      · left
        refine le_antisymm (fun k hk => ⟨hKI hk, (hker k).1 ?_⟩) hCK
        have h1 : π k ∈ K.map π := Subgroup.mem_map_of_mem π hk
        rw [h] at h1
        exact h1
      · right
        refine le_antisymm hKI fun i hi => ?_
        have h1 : π i ∈ K.map π := by rw [h, ← hπI]; exact Subgroup.mem_map_of_mem π hi
        obtain ⟨k, hk, hki⟩ := h1
        have h2 : k⁻¹ * i ∈ I ⊓ fixV Mp :=
          ⟨I.mul_mem (I.inv_mem (hKI hk)) hi,
            (hker _).1 (by rw [map_mul, map_inv, hki, inv_mul_cancel])⟩
        have e : i = k * (k⁻¹ * i) := by group
        rw [e]
        exact K.mul_mem hk (hCK h2)
  have hmem : I ∈ IrrPlus L (commV L) :=
    ⟨hIU, (isInv_iff L I).2 hIinv, by rw [commOf_eq_commSub]; exact hIcomm, hIrrSec⟩
  have hstab : ∀ g ∈ M ⊓ Subgroup.normalizer (L : Set (MulAut W)), ∀ w ∈ I, g w ∈ I := by
    intro g hg
    have hgP : ∀ p ∈ P, g p ∈ P := by
      intro p hp
      refine ⟨?_, map_mem_commV_of_normalizer hg.2 hp.2⟩
      show π (g p) ∈ J
      have h1 : (⟨g, hg.1⟩ : ↥M) • π p ∈ (⟨g, hg.1⟩ : ↥M) • J :=
        Subgroup.smul_mem_pointwise_smul _ _ _ hp.1
      rwa [hJN _ hg.2] at h1
    have hle : I ≤ I.comap g.toMonoidHom := by
      rw [hI, commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, p, hp, rfl⟩
      show g (x p * p⁻¹) ∈ I
      have hx' : g * x * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hg.2 x).1 hx
      have e : g (x p * p⁻¹) = (g * x * g⁻¹) (g p) * (g p)⁻¹ := by
        simp [MulAut.mul_apply]
      rw [e]
      exact Subgroup.subset_closure ⟨_, hx', g p, hgP p hp, rfl⟩
    exact fun w hw => hle hw
  exact ⟨I, hmem, fun g hg => mem_stabSub_of_inv (hstab g hg) (hstab g⁻¹ (inv_mem hg))⟩

end CFSG.Quasithin.RonanD321
