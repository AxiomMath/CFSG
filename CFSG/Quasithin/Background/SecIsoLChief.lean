module

public import CFSG.Quasithin.Background.B5Statement
import CFSG.Quasithin.Background.F918Z8Ex2a

public section

namespace CFSG.Quasithin

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

namespace SecIsoL

theorem symm {I Z I' Z' : Subgroup V} (h : SecIsoL L I Z I' Z') : SecIsoL L I' Z' I Z := by
  obtain ⟨hZI, -, hI, hZ, -, -, -⟩ := B5.secIsoL_iff.1 h
  exact secIsoL_of_common_section
    (B5.secIsoL_refl (fun x hx u hu => hI ⟨x, hx⟩ u hu)
      (fun x hx z hz => hZ ⟨x, hx⟩ z hz) hZI) h

theorem trans {I Z I' Z' I'' Z'' : Subgroup V} (h : SecIsoL L I Z I' Z')
    (h' : SecIsoL L I' Z' I'' Z'') : SecIsoL L I Z I'' Z'' :=
  secIsoL_of_common_section h' (symm h)

end SecIsoL

private def secPullback {I Z' I' : Subgroup V}
    (β : ↥I →* ↥I' ⧸ Z'.subgroupOf I') (J' : Subgroup V) : Subgroup V :=
  (((J'.subgroupOf I').map (QuotientGroup.mk' (Z'.subgroupOf I'))).comap β).map I.subtype

private theorem mem_pullback_image {I Z' I' : Subgroup V}
    (β : ↥I →* ↥I' ⧸ Z'.subgroupOf I') {J' : Subgroup V} {v : V} :
    v ∈ secPullback β J' ↔
      ∃ (u : ↥I) (m : ↥I'), (u : V) = v ∧ (m : V) ∈ J' ∧ β u = QuotientGroup.mk m := by
  rw [secPullback, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Subgroup.mem_comap] at hu
    obtain ⟨m, hm, hβu⟩ := Subgroup.mem_map.1 hu
    exact ⟨u, m, rfl, Subgroup.mem_subgroupOf.1 hm, hβu.symm⟩
  · rintro ⟨u, m, rfl, hm, hβu⟩
    refine ⟨u, Subgroup.mem_comap.2 (Subgroup.mem_map.2 ?_), rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.2 hm, hβu.symm⟩

private theorem secPullback_le {I Z' I' : Subgroup V}
    (β : ↥I →* ↥I' ⧸ Z'.subgroupOf I') (J' : Subgroup V) : secPullback β J' ≤ I := by
  intro v hv
  rw [mem_pullback_image] at hv
  obtain ⟨u, -, rfl, -⟩ := hv
  exact u.2

private theorem le_secPullback {I Z Z' I' : Subgroup V}
    (β : ↥I →* ↥I' ⧸ Z'.subgroupOf I') {J' : Subgroup V}
    (hZI : Z ≤ I) (hJ'I' : J' ≤ I')
    (hβk : ∀ u : ↥I, β u = 1 ↔ (u : V) ∈ Z) : Z ≤ secPullback β J' := by
  intro z hz
  rw [mem_pullback_image]
  refine ⟨⟨z, hZI hz⟩, ⟨1, hJ'I' (J'.one_mem)⟩, rfl, J'.one_mem, ?_⟩
  rw [show (⟨1, hJ'I' (J'.one_mem)⟩ : ↥I') = 1 from rfl, QuotientGroup.mk_one]
  exact (hβk ⟨z, hZI hz⟩).2 hz

private theorem isInv_secPullback {I Z' I' : Subgroup V}
    (β : ↥I →* ↥I' ⧸ Z'.subgroupOf I') {J' : Subgroup V}
    (hI : XMod.IsInv ↥L I) (hJ'I' : J' ≤ I') (hJ'inv : XMod.IsInv ↥L J')
    (hβe : ∀ (γ : ↥L) (u : ↥I) (m : ↥I') (hu : (γ : MulAut V) (u : V) ∈ I)
      (hm : (γ : MulAut V) (m : V) ∈ I'), β u = QuotientGroup.mk m →
        β ⟨(γ : MulAut V) (u : V), hu⟩ =
          QuotientGroup.mk ⟨(γ : MulAut V) (m : V), hm⟩) :
    XMod.IsInv ↥L (secPullback β J') := by
  intro γ v hv
  change (γ : MulAut V) v ∈ secPullback β J'
  rw [mem_pullback_image] at hv ⊢
  obtain ⟨u, m, hu, hmJ', hβu⟩ := hv
  have hmI' : (γ : MulAut V) (m : V) ∈ I' := hJ'I' (hJ'inv γ m hmJ')
  refine ⟨⟨(γ : MulAut V) (u : V), hI γ u u.2⟩,
    ⟨(γ : MulAut V) (m : V), hmI'⟩, ?_, hJ'inv γ m hmJ', ?_⟩
  · simp [hu]
  · exact hβe γ u m (hI γ u u.2) hmI' hβu

private theorem eq_of_secPullback_eq_left {I Z Z' I' : Subgroup V}
    (β : ↥I →* ↥I' ⧸ Z'.subgroupOf I') {J' : Subgroup V}
    (hβs : Function.Surjective β) (hβk : ∀ u : ↥I, β u = 1 ↔ (u : V) ∈ Z)
    (hZ'J' : Z' ≤ J') (hJ'I' : J' ≤ I') (h : secPullback β J' = Z) : J' = Z' := by
  apply le_antisymm _ hZ'J'
  intro m hmJ'
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk' (Z'.subgroupOf I') ⟨m, hJ'I' hmJ'⟩)
  have huJ : (u : V) ∈ secPullback β J' := by
    rw [mem_pullback_image]
    exact ⟨u, ⟨m, hJ'I' hmJ'⟩, rfl, hmJ', hu⟩
  have h1 : QuotientGroup.mk' (Z'.subgroupOf I') (⟨m, hJ'I' hmJ'⟩ : ↥I') = 1 := by
    rw [← hu]
    exact (hβk u).2 (h ▸ huJ)
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)

private theorem eq_of_secPullback_eq_right {I Z' I' : Subgroup V}
    (β : ↥I →* ↥I' ⧸ Z'.subgroupOf I') {J' : Subgroup V}
    (hβs : Function.Surjective β) (hZ'J' : Z' ≤ J') (hJ'I' : J' ≤ I')
    (h : secPullback β J' = I) : J' = I' := by
  apply le_antisymm hJ'I'
  intro m hmI'
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk' (Z'.subgroupOf I') ⟨m, hmI'⟩)
  have huJ : (u : V) ∈ secPullback β J' := by rw [h]; exact u.2
  rw [mem_pullback_image] at huJ
  obtain ⟨u', m', hu', hmJ', hβu'⟩ := huJ
  have h2 : QuotientGroup.mk' (Z'.subgroupOf I') m' =
      QuotientGroup.mk' (Z'.subgroupOf I') (⟨m, hmI'⟩ : ↥I') := by
    calc QuotientGroup.mk' (Z'.subgroupOf I') m' = β u' := hβu'.symm
      _ = β u := congrArg β (Subtype.ext hu')
      _ = QuotientGroup.mk' (Z'.subgroupOf I') (⟨m, hmI'⟩ : ↥I') := hu
  have hz : (m' : V)⁻¹ * (m : V) ∈ Z' := by
    have h3 := QuotientGroup.eq.1 h2
    simpa using Subgroup.mem_subgroupOf.1 h3
  have hmul : (m : V) = (m' : V) * ((m' : V)⁻¹ * (m : V)) := by group
  rw [hmul]
  exact J'.mul_mem hmJ' (hZ'J' hz)

private theorem lt_of_secIsoL_data {I Z I' Z' : Subgroup V}
    (β : ↥I →* ↥I' ⧸ Z'.subgroupOf I') (hZ'I' : Z' ≤ I')
    (hβk : ∀ u : ↥I, β u = 1 ↔ (u : V) ∈ Z) (hlt : Z < I) : Z' < I' := by
  refine lt_of_le_of_ne hZ'I' ?_
  intro heq
  obtain ⟨z, hzI, hzZ⟩ := (SetLike.lt_iff_le_and_exists.1 hlt).2
  have hzβ : β ⟨z, hzI⟩ ≠ 1 := fun hβ1 => hzZ ((hβk _).1 hβ1)
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨z, hzI⟩)
  apply hzβ
  rw [← hm]
  refine (QuotientGroup.eq_one_iff m).2 (Subgroup.mem_subgroupOf.2 ?_)
  rw [heq]
  exact m.2

private theorem isIrrSec_of_data {I Z I' Z' : Subgroup V}
    (hZI : Z ≤ I) (hZ'I' : Z' ≤ I') (hI : XMod.IsInv ↥L I)
    (β : ↥I →* ↥I' ⧸ Z'.subgroupOf I') (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥I, β u = 1 ↔ (u : V) ∈ Z)
    (hβe : ∀ (γ : ↥L) (u : ↥I) (m : ↥I') (hu : (γ : MulAut V) (u : V) ∈ I)
      (hm : (γ : MulAut V) (m : V) ∈ I'), β u = QuotientGroup.mk m →
        β ⟨(γ : MulAut V) (u : V), hu⟩ =
          QuotientGroup.mk ⟨(γ : MulAut V) (m : V), hm⟩)
    (hirr : XMod.IsIrrSec ↥L Z I) : XMod.IsIrrSec ↥L Z' I' := by
  obtain ⟨hlt, hbetween⟩ := hirr
  refine ⟨lt_of_secIsoL_data β hZ'I' hβk hlt, fun J' hJ'inv hZ'J' hJ'I' => ?_⟩
  have hZJ : Z ≤ secPullback β J' := le_secPullback β hZI hJ'I' hβk
  have hJI : secPullback β J' ≤ I := secPullback_le β J'
  have hJinv : XMod.IsInv ↥L (secPullback β J') :=
    isInv_secPullback β hI hJ'I' hJ'inv hβe
  rcases hbetween (secPullback β J') hJinv hZJ hJI with h | h
  · exact Or.inl (eq_of_secPullback_eq_left β hβs hβk hZ'J' hJ'I' h)
  · exact Or.inr (eq_of_secPullback_eq_right β hβs hZ'J' hJ'I' h)

namespace SecIsoL

theorem isIrrSec {I Z I' Z' : Subgroup V} (h : SecIsoL L I Z I' Z')
    (hirr : XMod.IsIrrSec ↥L Z I) : XMod.IsIrrSec ↥L Z' I' := by
  obtain ⟨hZI, hZ'I', hI, -, -, -, β, hβs, hβk, hβe⟩ := B5.secIsoL_iff.1 h
  exact isIrrSec_of_data hZI hZ'I' hI β hβs hβk hβe hirr

theorem not_commOf_le {I Z I' Z' : Subgroup V} (h : SecIsoL L I Z I' Z')
    (hnc : ¬ XMod.commOf ↥L I ≤ Z) : ¬ XMod.commOf ↥L I' ≤ Z' := by
  intro hle
  obtain ⟨hZI, -, hI, hZ, hI', hZ', β, hβs, hβk, hβe⟩ := B5.secIsoL_iff.1 h
  apply hnc
  rw [XMod.commOf, Subgroup.closure_le]
  rintro c ⟨γ, u, hu, rfl⟩
  change ((γ : MulAut V) (u : V)) * (u : V)⁻¹ ∈ Z
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, hu⟩)
  have hγm : (γ : MulAut V) (m : V) ∈ I' := hI' γ m m.2
  have he := hβe γ ⟨u, hu⟩ m (hI γ u hu) hγm hm.symm
  have hgen : ((γ : MulAut V) (u : V)) * (u : V)⁻¹ ∈ Z := by
    apply (hβk ⟨(γ : MulAut V) (u : V) * (u : V)⁻¹,
      I.mul_mem (hI γ u hu) (I.inv_mem hu)⟩).1
    have hprod : β (⟨(γ : MulAut V) (u : V) * (u : V)⁻¹,
        I.mul_mem (hI γ u hu) (I.inv_mem hu)⟩ : ↥I) =
        β (⟨(γ : MulAut V) (u : V), hI γ u hu⟩ * ⟨u, hu⟩⁻¹) := by
      congr 1
    rw [hprod, map_mul, map_inv, he, ← hm, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h := hle (Subgroup.subset_closure ⟨γ, m, m.2, rfl⟩)
    change ((γ : MulAut V) (m : V)) * (m : V)⁻¹ ∈ Z' at h
    exact h
  exact hgen

end SecIsoL

private theorem secIsoL_of_sup_eq {A B C : Subgroup V}
    (hA : XMod.IsInv ↥L A) (hB : XMod.IsInv ↥L B) (hC : XMod.IsInv ↥L C)
    (hABC : C = A ⊔ B) : SecIsoL L A (A ⊓ B) C B := by
  let β : ↥A →* ↥C ⧸ B.subgroupOf C :=
    (QuotientGroup.mk' (B.subgroupOf C)).comp
      (Subgroup.inclusion (by rw [hABC]; exact le_sup_left))
  have hβ : ∀ a : ↥A, β a = QuotientGroup.mk' (B.subgroupOf C)
      (Subgroup.inclusion (by rw [hABC]; exact le_sup_left) a) := fun _ => rfl
  rw [B5.secIsoL_iff]
  refine ⟨inf_le_left, by rw [hABC]; exact le_sup_right, fun h u hu => hA h u hu,
    fun h z hz => (XMod.IsInv.inf hA hB) h z hz, fun h c hc => hC h c hc,
    fun h b hb => hB h b hb, β, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    have hc : (c : V) ∈ A ⊔ B := by rw [← hABC]; exact c.2
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hc
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hβ, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (a : V)⁻¹ * (c : V) ∈ B
    rw [← hab]
    simpa using hb
  · intro a
    rw [hβ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    exact ⟨fun hb => ⟨a.2, hb⟩, fun hb => hb.2⟩
  · intro γ a c ha hc hac
    have h1 : QuotientGroup.mk' (B.subgroupOf C)
        (Subgroup.inclusion (by rw [hABC]; exact le_sup_left) a) =
        QuotientGroup.mk' (B.subgroupOf C) c := by
      rw [← hβ]
      exact hac
    have hmem : (a : V)⁻¹ * (c : V) ∈ B := by
      have := QuotientGroup.eq.1 h1
      simpa using Subgroup.mem_subgroupOf.1 this
    have hmem' : ((γ : MulAut V) (a : V))⁻¹ * ((γ : MulAut V) (c : V)) ∈ B := by
      have h := hB γ ((a : V)⁻¹ * (c : V)) hmem
      change (γ : MulAut V) ((a : V)⁻¹ * (c : V)) ∈ B at h
      simpa [map_mul, map_inv] using h
    rw [hβ, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hmem'

theorem FFModel.Realizes.of_secIsoL {D : FFModel} {I Z I' Z' : Subgroup V}
    (hD : D.Realizes L I' Z') (h : SecIsoL L I Z I' Z') : D.Realizes L I Z := by
  obtain ⟨π, hπ⟩ := hD
  exact ⟨π, d321i_realizesVia_of_secIsoL hπ h⟩

private theorem le_of_inf_le_of_sec {M M' I Z : Subgroup V}
    (hM' : XMod.IsInv ↥L M') (hZ : XMod.IsInv ↥L Z)
    (hirrM : XMod.IsIrrSec ↥L M' M) (hIM : I ≤ M) (hZI : Z ≤ I)
    (hirr : XMod.IsIrrSec ↥L Z I) (hinf : I ⊓ M' ≤ Z) : Z ≤ M' := by
  by_contra hle
  have hne : Z ⊔ M' ≠ M' := fun h => hle (by rw [← h]; exact le_sup_left)
  have hJinv : XMod.IsInv ↥L (Z ⊔ M') := XMod.IsInv.sup hZ hM'
  have hJleM : Z ⊔ M' ≤ M := sup_le (hZI.trans hIM) hirrM.1.le
  rcases hirrM.2 (Z ⊔ M') hJinv le_sup_right hJleM with h | h
  · exact hne h
  · have hIZ : I ≤ Z := by
      intro i hi
      have hiM : i ∈ M := hIM hi
      rw [← h] at hiM
      obtain ⟨z, hz, m, hm, hzm⟩ := Subgroup.mem_sup.1 hiM
      have hmI : m ∈ I := by
        have hm_eq : m = z⁻¹ * i := by rw [← hzm]; group
        rw [hm_eq]
        exact I.mul_mem (I.inv_mem (hZI hz)) hi
      have hmZ : m ∈ Z := hinf ⟨hmI, hm⟩
      rw [← hzm]
      exact Z.mul_mem hz hmZ
    exact hirr.1.ne' (le_antisymm hIZ hZI)

theorem secIsoL_or_secIsoL_inf {M M' I Z : Subgroup V} (hM : XMod.IsInv ↥L M)
    (hM' : XMod.IsInv ↥L M') (hirrM : XMod.IsIrrSec ↥L M' M) (hIM : I ≤ M)
    (hI : XMod.IsInv ↥L I) (hZ : XMod.IsInv ↥L Z) (hirr : XMod.IsIrrSec ↥L Z I) :
    SecIsoL L I Z M M' ∨ SecIsoL L I Z (I ⊓ M') (Z ⊓ M') := by
  have hZI : Z ≤ I := hirr.1.le
  by_cases hinf : I ⊓ M' ≤ Z
  · have hZleM' : Z ≤ M' := le_of_inf_le_of_sec hM' hZ hirrM hIM hZI hirr hinf
    have hInf : I ⊓ M' = Z := le_antisymm hinf (le_inf hZI hZleM')
    have hSup : I ⊔ M' = M := by
      rcases hirrM.2 (I ⊔ M') (XMod.IsInv.sup hI hM') le_sup_right
        (sup_le hIM hirrM.1.le) with h | h
      · exfalso
        have hIle : I ≤ M' := by rw [← h]; exact le_sup_left
        have hIZ : I ≤ Z := by simpa [(inf_eq_left).2 hIle] using hinf
        exact hirr.1.ne' (le_antisymm hIZ hZI)
      · exact h
    left
    have h := secIsoL_of_sup_eq hI hM' hM hSup.symm
    rwa [hInf] at h
  · have hSup : (I ⊓ M') ⊔ Z = I := by
      have hne : (I ⊓ M') ⊔ Z ≠ Z := by
        intro h
        apply hinf
        rw [← h]
        exact le_sup_left
      rcases hirr.2 ((I ⊓ M') ⊔ Z) (XMod.IsInv.sup (XMod.IsInv.inf hI hM') hZ)
        le_sup_right (sup_le inf_le_left hZI) with h | h
      · exact absurd h hne
      · exact h
    right
    have h := secIsoL_of_sup_eq (XMod.IsInv.inf hI hM') hZ hI hSup.symm
    rw [show (I ⊓ M') ⊓ Z = Z ⊓ M' by
      rw [inf_comm, ← inf_assoc, (inf_eq_left).2 hZI]] at h
    exact SecIsoL.symm h

end CFSG.Quasithin
