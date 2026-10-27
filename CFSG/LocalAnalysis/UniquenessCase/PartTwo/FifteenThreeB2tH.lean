module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB
import CFSG.Quasithin.EmptyFaithful.SmithD391Decomp
import CFSG.Quasithin.Background.InternalSecSum
import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Homogeneous

variable {W : Type} [CommGroup W] [Finite W]

private lemma s15_Three_isIrr_iff (A : Subgroup (MulAut W)) (J : Subgroup W) :
    IsIrrOn A J ⊥ ↔ XMod.IsIrr ↥A J := by
  unfold IsIrrOn XMod.IsIrr XMod.IsIrrSec XMod.IsInv StableUnder
  constructor
  · rintro ⟨hlt, hstab, -, hmin⟩
    exact ⟨fun a j hj => hstab a a.2 j hj, hlt,
      fun J' hJ' _ hJ'J => hmin J' (fun a ha u hu => hJ' ⟨a, ha⟩ u hu) bot_le hJ'J⟩
  · rintro ⟨hinv, hlt, hmin⟩
    exact ⟨hlt, (fun a ha u hu => hinv ⟨a, ha⟩ u hu),
      (fun a _ u hu => by rw [Subgroup.mem_bot] at hu ⊢; rw [hu, map_one]),
      fun J' hJ' _ hJ'J => hmin J' (fun a u hu => hJ' (a : MulAut W) a.2 u hu) bot_le hJ'J⟩

private lemma s15_Three_secIso_of_secIsoL {A : Subgroup (MulAut W)} {J J' : Subgroup W}
    (h : SecIsoL A J ⊥ J' ⊥) : s15SecIso A J ⊥ J' ⊥ := by
  obtain ⟨-, -, -, -, -, -, β, hs, hk, he⟩ := (CFSG.Quasithin.B5.secIsoL_iff).1 h
  exact ⟨β, hs, hk, fun x hx u u' hu hu' hβ => he ⟨x, hx⟩ u u' hu hu' hβ⟩

private lemma s15_Three_secIso_of_iso {A : Subgroup (MulAut W)} {J J' : Subgroup W}
    (hJ : XMod.IsInv ↥A J) (hJ' : XMod.IsInv ↥A J') (h : XMod.Iso ↥A J J') :
    s15SecIso A J ⊥ J' ⊥ :=
  s15_Three_secIso_of_secIsoL (CFSG.Quasithin.B5.secIsoL_of_iso hJ hJ' h)

private lemma s15_Three_iso_of_secIso {A : Subgroup (MulAut W)} {J J' : Subgroup W}
    (hJ : XMod.IsInv ↥A J) (hJ' : XMod.IsInv ↥A J') (h : s15SecIso A J ⊥ J' ⊥) :
    XMod.Iso ↥A J J' := by
  have hL : SecIsoL A J ⊥ J' ⊥ := by
    rw [CFSG.Quasithin.B5.secIsoL_iff]
    obtain ⟨β, hs, hk, he⟩ := h
    exact ⟨bot_le, bot_le, (fun k u hu => hJ k u hu),
      (fun k z hz => by rw [Subgroup.mem_bot] at hz; rw [hz, map_one]; exact Subgroup.one_mem _),
      (fun k m hm => hJ' k m hm),
      (fun k z hz => by rw [Subgroup.mem_bot] at hz; rw [hz, map_one]; exact Subgroup.one_mem _),
      β, hs, hk, fun γ u m hu hm hβ => he γ γ.2 u m hu hm hβ⟩
  obtain ⟨e, he⟩ := InternalSec.equiv_of_secIsoL hL
  refine ⟨e, fun a l l' hl => ?_⟩
  have hw : (a : MulAut W) (l : W) ∈ J := by
    change a • (l : W) ∈ J
    rw [hl]
    exact l'.2
  have hw' : (a : MulAut W) ((e l : ↥J') : W) ∈ J' := hJ' a (e l) (e l).2
  have h1 := he a l hw hw'
  have h2 : (⟨(a : MulAut W) (l : W), hw⟩ : ↥J) = l' := Subtype.ext hl
  rw [h2] at h1
  show (a : MulAut W) ((e l : ↥J') : W) = ((e l' : ↥J') : W)
  exact (congrArg (fun x : ↥J' => (x : W)) h1).symm

private lemma s15_Three_secIso_refl {A : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : IsIrrOn A J ⊥) : s15SecIso A J ⊥ J ⊥ :=
  s15_Three_secIso_of_iso ((s15_Three_isIrr_iff A J).1 hJ).1
    ((s15_Three_isIrr_iff A J).1 hJ).1 (XMod.Iso.refl J)

private lemma s15_Three_secIso_symm {A : Subgroup (MulAut W)} {J J' : Subgroup W}
    (hJ : IsIrrOn A J ⊥) (hJ' : IsIrrOn A J' ⊥) (h : s15SecIso A J ⊥ J' ⊥) :
    s15SecIso A J' ⊥ J ⊥ :=
  s15_Three_secIso_of_iso ((s15_Three_isIrr_iff A J').1 hJ').1
    ((s15_Three_isIrr_iff A J).1 hJ).1
    (XMod.Iso.symm ((s15_Three_isIrr_iff A J).1 hJ).1
      (s15_Three_iso_of_secIso ((s15_Three_isIrr_iff A J).1 hJ).1
        ((s15_Three_isIrr_iff A J').1 hJ').1 h))

private lemma s15_Three_secIso_trans {A : Subgroup (MulAut W)} {J J' J'' : Subgroup W}
    (hJ : IsIrrOn A J ⊥) (hJ' : IsIrrOn A J' ⊥) (hJ'' : IsIrrOn A J'' ⊥)
    (h : s15SecIso A J ⊥ J' ⊥) (h' : s15SecIso A J' ⊥ J'' ⊥) :
    s15SecIso A J ⊥ J'' ⊥ :=
  s15_Three_secIso_of_iso ((s15_Three_isIrr_iff A J).1 hJ).1
    ((s15_Three_isIrr_iff A J'').1 hJ'').1
    (XMod.Iso.trans
      (s15_Three_iso_of_secIso ((s15_Three_isIrr_iff A J).1 hJ).1
        ((s15_Three_isIrr_iff A J').1 hJ').1 h)
      (s15_Three_iso_of_secIso ((s15_Three_isIrr_iff A J').1 hJ').1
        ((s15_Three_isIrr_iff A J'').1 hJ'').1 h'))

private lemma s15_Three_irr_map_of_normalizes {A : Subgroup (MulAut W)} {n : MulAut W}
    (hn : s15Normalizes n A) {J : Subgroup W} (hJ : IsIrrOn A J ⊥) :
    IsIrrOn A (J.map n.toMonoidHom) ⊥ := by
  have hcomp : (n⁻¹).toMonoidHom.comp n.toMonoidHom = MonoidHom.id W := by
    ext w; simp
  have hcomp' : n.toMonoidHom.comp (n⁻¹).toMonoidHom = MonoidHom.id W := by
    ext w; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro h0
    have h1 : J = ⊥ := by
      have h2 := congrArg (Subgroup.map (n⁻¹).toMonoidHom) h0
      rw [Subgroup.map_map, hcomp, Subgroup.map_id, Subgroup.map_bot] at h2
      exact h2
    exact hJ.1.ne' h1
  · intro a ha u hu
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hu
    have hb : n⁻¹ * a * n ∈ A := (hn (n⁻¹ * a * n)).mpr (by simpa [mul_assoc] using ha)
    exact Subgroup.mem_map.2
      ⟨(n⁻¹ * a * n) j, hJ.2.1 _ hb j hj, by simp [MulAut.mul_apply]⟩
  · intro a _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro K hK _ hKle
    set K' : Subgroup W := K.map (n⁻¹).toMonoidHom with hK'
    have hK'le : K' ≤ J := by
      have h := Subgroup.map_mono (f := (n⁻¹).toMonoidHom) hKle
      rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h
      rw [hK']
      exact h
    have hK'stab : StableUnder A K' := by
      intro a ha u hu
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hu
      have hb : n * a * n⁻¹ ∈ A := (hn a).mp ha
      exact Subgroup.mem_map.2
        ⟨(n * a * n⁻¹) k, hK _ hb k hk, by simp [MulAut.mul_apply]⟩
    rcases hJ.2.2.2 K' hK'stab bot_le hK'le with h0 | hjeq
    · left
      have h1 := congrArg (Subgroup.map n.toMonoidHom) h0
      rw [hK', Subgroup.map_map, hcomp', Subgroup.map_id, Subgroup.map_bot] at h1
      exact h1
    · right
      have h1 := congrArg (Subgroup.map n.toMonoidHom) hjeq
      rw [hK', Subgroup.map_map, hcomp', Subgroup.map_id] at h1
      exact h1

private lemma s15_Three_normalizes_action {A N : Subgroup (MulAut W)}
    (hN : ∀ n ∈ N, s15Normalizes n A) : XMod.Normalizes ↥A ↥N W := by
  intro n a
  refine ⟨⟨(n : MulAut W) * (a : MulAut W) * (n : MulAut W)⁻¹,
    (hN n n.2 (a : MulAut W)).mp a.2⟩, fun q => ?_⟩
  show (n : MulAut W) ((a : MulAut W) q) =
    ((n : MulAut W) * (a : MulAut W) * (n : MulAut W)⁻¹) ((n : MulAut W) q)
  simp [MulAut.mul_apply]

private lemma s15_Three_toMonoidEnd_coe {N : Subgroup (MulAut W)} (n : ↥N) :
    ((MulDistribMulAction.toMonoidEnd ↥N W) n : W →* W) = (n : MulAut W).toMonoidHom := by
  ext q
  change n • q = (n : MulAut W) q
  rw [Submonoid.smul_def, MulAut.smul_def]

private lemma s15_Three_iso_map_conj {A N : Subgroup (MulAut W)}
    (hN : ∀ n ∈ N, s15Normalizes n A) {n : MulAut W} (hn : n ∈ N)
    {J J' : Subgroup W} (h : XMod.Iso ↥A J J') :
    XMod.Iso ↥A (J.map n.toMonoidHom) (J'.map n.toMonoidHom) := by
  have hNorm := s15_Three_normalizes_action hN
  have h' := XMod.iso_smul hNorm (⟨n, hn⟩ : ↥N) h
  rwa [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def,
    s15_Three_toMonoidEnd_coe (N := N) ⟨n, hn⟩] at h'

private lemma s15_Three_secIso_map_conj {A N : Subgroup (MulAut W)}
    (hN : ∀ n ∈ N, s15Normalizes n A) {n : MulAut W} (hn : n ∈ N) {J J' : Subgroup W}
    (hJ : IsIrrOn A J ⊥) (hJ' : IsIrrOn A J' ⊥) (h : s15SecIso A J ⊥ J' ⊥) :
    s15SecIso A (J.map n.toMonoidHom) ⊥ (J'.map n.toMonoidHom) ⊥ := by
  have hJm : IsIrrOn A (J.map n.toMonoidHom) ⊥ := s15_Three_irr_map_of_normalizes (hN n hn) hJ
  have hJm' : IsIrrOn A (J'.map n.toMonoidHom) ⊥ := s15_Three_irr_map_of_normalizes (hN n hn) hJ'
  exact s15_Three_secIso_of_iso ((s15_Three_isIrr_iff A _).1 hJm).1
    ((s15_Three_isIrr_iff A _).1 hJm').1
    (s15_Three_iso_map_conj hN hn
      (s15_Three_iso_of_secIso ((s15_Three_isIrr_iff A J).1 hJ).1
        ((s15_Three_isIrr_iff A J').1 hJ').1 h))

private lemma s15_Three_secIso_exists_of_le_sSup {A : Subgroup (MulAut W)}
    {S : Set (Subgroup W)} (hS : ∀ J ∈ S, IsIrrOn A J ⊥) {K : Subgroup W}
    (hK : IsIrrOn A K ⊥) (hle : K ≤ sSup S) : ∃ J ∈ S, s15SecIso A K ⊥ J ⊥ := by
  have hS' : ∀ i : S, XMod.IsIrr ↥A (i : Subgroup W) :=
    fun i => (s15_Three_isIrr_iff A i).1 (hS i i.2)
  have hK' : XMod.IsIrr ↥A K := (s15_Three_isIrr_iff A K).1 hK
  have hle' : K ≤ ⨆ i : S, (i : Subgroup W) := by rwa [sSup_eq_iSup'] at hle
  obtain ⟨i, hiso⟩ := SmithD391.exists_iso_of_le_iSup (A := ↥A)
    (S := fun i : S => (i : Subgroup W)) hS' hK' hle'
  exact ⟨i, i.2, s15_Three_secIso_of_iso ((s15_Three_isIrr_iff A K).1 hK).1
    ((s15_Three_isIrr_iff A i).1 (hS i i.2)).1 hiso⟩

theorem s15_Three_homog_split {A N : Subgroup (MulAut W)}
    (hN : ∀ n ∈ N, s15Normalizes n A) (hsemi : s15Semisimple A) {I I' : Subgroup W}
    (hI : IsIrrOn A I ⊥) (hI' : IsIrrOn A I' ⊥)
    (hno : ∀ n ∈ N, ¬ s15SecIso A (I.map n.toMonoidHom) ⊥ I' ⊥) :
    ∃ P Q : Subgroup W, StableUnder A P ∧ StableUnder A Q ∧ StableUnder N P ∧
      StableUnder N Q ∧ P ⊓ Q = ⊥ ∧ P ⊔ Q = ⊤ ∧ I ≤ P ∧ I' ≤ Q := by
  set S_P : Set (Subgroup W) :=
    {J | IsIrrOn A J ⊥ ∧ ∃ n ∈ N, s15SecIso A (J.map n.toMonoidHom) ⊥ I ⊥} with hS_P
  set S_Q : Set (Subgroup W) :=
    {J | IsIrrOn A J ⊥ ∧ ¬ ∃ n ∈ N, s15SecIso A (J.map n.toMonoidHom) ⊥ I ⊥} with hS_Q
  have hS_Pirr : ∀ J ∈ S_P, IsIrrOn A J ⊥ := fun J hJ => by rw [hS_P] at hJ; exact hJ.1
  have hS_Qirr : ∀ J ∈ S_Q, IsIrrOn A J ⊥ := fun J hJ => by rw [hS_Q] at hJ; exact hJ.1
  have hPstabA : StableUnder A (sSup S_P) :=
    s15_Three_stableUnder_sSup fun J hJ => (hS_Pirr J hJ).2.1
  have hQstabA : StableUnder A (sSup S_Q) :=
    s15_Three_stableUnder_sSup fun J hJ => (hS_Qirr J hJ).2.1
  have hmapP : ∀ n ∈ N, ∀ J ∈ S_P, J.map n.toMonoidHom ∈ S_P := by
    intro n hn J hJ
    rw [hS_P] at hJ ⊢
    obtain ⟨hJirr, n₀, hn₀, hiso⟩ := hJ
    refine ⟨s15_Three_irr_map_of_normalizes (hN n hn) hJirr, n₀ * n⁻¹,
      N.mul_mem hn₀ (N.inv_mem hn), ?_⟩
    have hcomp : (n₀ * n⁻¹).toMonoidHom.comp n.toMonoidHom = n₀.toMonoidHom := by
      ext w; simp
    rwa [Subgroup.map_map, hcomp]
  have hmapQ : ∀ n ∈ N, ∀ J ∈ S_Q, J.map n.toMonoidHom ∈ S_Q := by
    intro n hn J hJ
    rw [hS_Q] at hJ ⊢
    obtain ⟨hJirr, hJnot⟩ := hJ
    refine ⟨s15_Three_irr_map_of_normalizes (hN n hn) hJirr, ?_⟩
    rintro ⟨n', hn', hiso'⟩
    apply hJnot
    refine ⟨n' * n, N.mul_mem hn' hn, ?_⟩
    rw [Subgroup.map_map] at hiso'
    exact hiso'
  have hPstabN : StableUnder N (sSup S_P) := by
    intro n hn u hu
    rw [sSup_eq_iSup'] at hu ⊢
    refine Subgroup.iSup_induction (fun Y : S_P => (Y : Subgroup W))
      (C := fun z => n z ∈ ⨆ Y : S_P, (Y : Subgroup W)) hu ?_ ?_ ?_
    · intro Y uY huY
      exact Subgroup.mem_iSup_of_mem ⟨Y.1.map n.toMonoidHom, hmapP n hn Y.1 Y.2⟩
        (Subgroup.mem_map.2 ⟨uY, huY, rfl⟩)
    · rw [map_one]; exact Subgroup.one_mem _
    · intro x y hx hy; rw [map_mul]; exact mul_mem hx hy
  have hQstabN : StableUnder N (sSup S_Q) := by
    intro n hn u hu
    rw [sSup_eq_iSup'] at hu ⊢
    refine Subgroup.iSup_induction (fun Y : S_Q => (Y : Subgroup W))
      (C := fun z => n z ∈ ⨆ Y : S_Q, (Y : Subgroup W)) hu ?_ ?_ ?_
    · intro Y uY huY
      exact Subgroup.mem_iSup_of_mem ⟨Y.1.map n.toMonoidHom, hmapQ n hn Y.1 Y.2⟩
        (Subgroup.mem_map.2 ⟨uY, huY, rfl⟩)
    · rw [map_one]; exact Subgroup.one_mem _
    · intro x y hx hy; rw [map_mul]; exact mul_mem hx hy
  have hcover : sSup S_P ⊔ sSup S_Q = ⊤ := by
    have hset : {J : Subgroup W | IsIrrOn A J ⊥} = S_P ∪ S_Q := by
      ext J
      rw [hS_P, hS_Q]
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro hJirr
        by_cases h : ∃ n ∈ N, s15SecIso A (J.map n.toMonoidHom) ⊥ I ⊥
        · exact Or.inl ⟨hJirr, h⟩
        · exact Or.inr ⟨hJirr, h⟩
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    have hsup := s15_Three_sSup_irr_le hsemi (X := ⊤) (fun _ _ u _ => Subgroup.mem_top u)
    have hset2 : {J : Subgroup W | IsIrrOn A J ⊥ ∧ J ≤ ⊤} = {J | IsIrrOn A J ⊥} := by
      ext J; simp
    rw [hset2, hset, sSup_union] at hsup
    exact hsup
  have hPinfQ : sSup S_P ⊓ sSup S_Q = ⊥ := by
    by_contra hne
    have hstab : StableUnder A (sSup S_P ⊓ sSup S_Q) :=
      fun a ha u hu => ⟨hPstabA a ha u hu.1, hQstabA a ha u hu.2⟩
    obtain ⟨K, hKle, hKirr⟩ := s15_Three_exists_irr_le hstab hne
    have hKP : K ≤ sSup S_P := hKle.trans inf_le_left
    have hKQ : K ≤ sSup S_Q := hKle.trans inf_le_right
    obtain ⟨J₀, hJ₀S, hiso₀⟩ := s15_Three_secIso_exists_of_le_sSup hS_Pirr hKirr hKP
    obtain ⟨J₁, hJ₁S, hiso₁⟩ := s15_Three_secIso_exists_of_le_sSup hS_Qirr hKirr hKQ
    rw [hS_P] at hJ₀S
    obtain ⟨hJ₀irr, n₀, hn₀, hisoJ₀⟩ := hJ₀S
    rw [hS_Q] at hJ₁S
    obtain ⟨hJ₁irr, hJ₁not⟩ := hJ₁S
    have hKIn₀ : s15SecIso A (K.map n₀.toMonoidHom) ⊥ I ⊥ :=
      s15_Three_secIso_trans (s15_Three_irr_map_of_normalizes (hN n₀ hn₀) hKirr)
        (s15_Three_irr_map_of_normalizes (hN n₀ hn₀) hJ₀irr) hI
        (s15_Three_secIso_map_conj hN hn₀ hKirr hJ₀irr hiso₀) hisoJ₀
    have hiso₁n : s15SecIso A (J₁.map n₀.toMonoidHom) ⊥ (K.map n₀.toMonoidHom) ⊥ :=
      s15_Three_secIso_symm (s15_Three_irr_map_of_normalizes (hN n₀ hn₀) hKirr)
        (s15_Three_irr_map_of_normalizes (hN n₀ hn₀) hJ₁irr)
        (s15_Three_secIso_map_conj hN hn₀ hKirr hJ₁irr hiso₁)
    exact hJ₁not ⟨n₀, hn₀,
      s15_Three_secIso_trans (s15_Three_irr_map_of_normalizes (hN n₀ hn₀) hJ₁irr)
        (s15_Three_irr_map_of_normalizes (hN n₀ hn₀) hKirr) hI hiso₁n hKIn₀⟩
  have hIP : I ≤ sSup S_P := by
    refine le_sSup ?_
    rw [hS_P]
    refine ⟨hI, 1, N.one_mem, ?_⟩
    rw [show (1 : MulAut W).toMonoidHom = MonoidHom.id W from rfl, Subgroup.map_id]
    exact s15_Three_secIso_refl hI
  have hI'Q : I' ≤ sSup S_Q := by
    refine le_sSup ?_
    rw [hS_Q]
    refine ⟨hI', ?_⟩
    rintro ⟨m, hm, hmiso⟩
    have hsym : s15SecIso A I ⊥ (I'.map m.toMonoidHom) ⊥ :=
      s15_Three_secIso_symm (s15_Three_irr_map_of_normalizes (hN m hm) hI') hI hmiso
    have hconj : s15SecIso A (I.map (m⁻¹).toMonoidHom) ⊥
        ((I'.map m.toMonoidHom).map (m⁻¹).toMonoidHom) ⊥ :=
      s15_Three_secIso_map_conj hN (N.inv_mem hm) hI
        (s15_Three_irr_map_of_normalizes (hN m hm) hI') hsym
    have hcomp : (m⁻¹).toMonoidHom.comp m.toMonoidHom = MonoidHom.id W := by ext w; simp
    have htarget : (I'.map m.toMonoidHom).map (m⁻¹).toMonoidHom = I' := by
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [htarget] at hconj
    exact hno m⁻¹ (N.inv_mem hm) hconj
  exact ⟨sSup S_P, sSup S_Q, hPstabA, hQstabA, hPstabN, hQstabN, hPinfQ, hcover, hIP, hI'Q⟩

end Homogeneous

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
