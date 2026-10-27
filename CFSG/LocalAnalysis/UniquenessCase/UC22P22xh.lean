module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def preMbar (D : Data G) (Y : Subgroup (MBar D.M D.U)) : Subgroup G :=
  (Y.comap (QuotientGroup.mk' (kerAct D.M D.U).normalCore)).map D.M.subtype

namespace P22x

section Group

theorem mem_preMbar (D : Data G) {Y : Subgroup (MBar D.M D.U)} {x : G} :
    x ∈ preMbar D Y ↔ ∃ h : x ∈ D.M, (QuotientGroup.mk ⟨x, h⟩ : MBar D.M D.U) ∈ Y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨h, hY⟩
    exact ⟨⟨x, h⟩, hY, rfl⟩

theorem preMbar_le_M (D : Data G) (Y : Subgroup (MBar D.M D.U)) : preMbar D Y ≤ D.M :=
  Subgroup.map_subtype_le _

theorem mbarImage_preMbar (D : Data G) (Y : Subgroup (MBar D.M D.U)) :
    mbarImage D.M D.U (preMbar D Y) = Y := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ((mem_preMbar D).1 hz).2
  · intro a ha
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨z, (mem_preMbar D).2 ⟨z.2, ha⟩, rfl⟩

theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {n : G} (hn : n ∈ normalizer (A : Set G)) :
    A.map (MulAut.conj n).toMonoidHom = A := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hn a).1 ha
  · intro hz
    refine ⟨n⁻¹ * z * n, ?_, by simp [mul_assoc]⟩
    exact (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * z * n)).2 (by simpa [mul_assoc] using hz)

theorem mem_normalizer_commutator {A B : Subgroup G} {n : G} (hA : n ∈ normalizer (A : Set G))
    (hB : n ∈ normalizer (B : Set G)) : n ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have hmap : (⁅A, B⁆ : Subgroup G).map (MulAut.conj n).toMonoidHom = ⁅A, B⁆ := by
    rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hA,
      map_conj_eq_of_mem_normalizer hB]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← hmap]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← hmap] at hh
    obtain ⟨c, hc, hch⟩ := hh
    have : c = h := (MulAut.conj n).injective hch
    rwa [this] at hc

theorem mem_normalizer_preMbar (D : Data G) {Y : Subgroup (MBar D.M D.U)} {y : G} (hy : y ∈ D.M)
    (hyY : (QuotientGroup.mk ⟨y, hy⟩ : MBar D.M D.U) ∈ normalizer (Y : Set (MBar D.M D.U))) :
    y ∈ normalizer (preMbar D Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨hzM, hzY⟩ := (mem_preMbar D).1 hz
    refine (mem_preMbar D).2 ⟨D.M.mul_mem (D.M.mul_mem hy hzM) (D.M.inv_mem hy), ?_⟩
    have := (Subgroup.mem_normalizer_iff.1 hyY _).1 hzY
    have e : (QuotientGroup.mk ⟨y * z * y⁻¹, D.M.mul_mem (D.M.mul_mem hy hzM) (D.M.inv_mem hy)⟩ :
        MBar D.M D.U) = QuotientGroup.mk ⟨y, hy⟩ * QuotientGroup.mk ⟨z, hzM⟩ *
          (QuotientGroup.mk ⟨y, hy⟩)⁻¹ := rfl
    rwa [e]
  · intro hz
    obtain ⟨hzM, hzY⟩ := (mem_preMbar D).1 hz
    have hzM' : z ∈ D.M := by
      have := D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hy) hzM) hy
      simpa [mul_assoc] using this
    refine (mem_preMbar D).2 ⟨hzM', ?_⟩
    have e : (QuotientGroup.mk ⟨y * z * y⁻¹, hzM⟩ : MBar D.M D.U) =
        QuotientGroup.mk ⟨y, hy⟩ * QuotientGroup.mk ⟨z, hzM'⟩ *
          (QuotientGroup.mk ⟨y, hy⟩)⁻¹ := rfl
    rw [e] at hzY
    exact (Subgroup.mem_normalizer_iff.1 hyY _).2 hzY

theorem mem_normalizer_inf {A B : Subgroup G} {n : G} (hA : n ∈ normalizer (A : Set G))
    (hB : n ∈ normalizer (B : Set G)) : n ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  exact and_congr (Subgroup.mem_normalizer_iff.1 hA h) (Subgroup.mem_normalizer_iff.1 hB h)

end Group

section Module2

variable {X : Type} [Group X] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Nbar : Subgroup X} {m : ℕ} {Nb : Fin m → Subgroup X}

theorem NatDec.proj_mono (d : NatDec ρ Nbar Nb) (i : Fin m) {A B : Subgroup X} (h : A ≤ B) :
    d.proj i A ≤ d.proj i B := by
  intro b hb
  obtain ⟨f, hf, rfl⟩ := (d.mem_proj i).1 hb
  exact (d.mem_proj i).2 ⟨f, h hf, rfl⟩

theorem NatDec.commOn_proj (d : NatDec ρ Nbar Nb) (i : Fin m) {A : Subgroup X} (hA : A ≤ Nbar) :
    commOn ρ A (natIi ρ Nbar (Nb i)) = commOn ρ (d.proj i A) (natIi ρ Nbar (Nb i)) := by
  apply le_antisymm
  · rw [commOn_le_iff]
    intro a ha y hy
    obtain ⟨b, hb, hab⟩ := d.exists_proj_act i hA ha hy
    rw [hab]
    exact sub_mem_commOn hb hy
  · rw [commOn_le_iff]
    intro b hb y hy
    obtain ⟨a, ha, hab⟩ := d.exists_act_of_proj i hb hy
    rw [← hab]
    exact sub_mem_commOn ha hy

@[expose] def trivSub (ρ : Representation (ZMod 2) X V) (S : Submodule (ZMod 2) V) : Subgroup X where
  carrier := {a | ∀ y ∈ S, ρ a y = y}
  mul_mem' {a b} ha hb y hy := by
    rw [map_mul, Module.End.mul_apply, hb y hy, ha y hy]
  one_mem' y _ := by simp
  inv_mem' {a} ha y hy := by
    conv_lhs => rw [← ha y hy]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end Module2

section Claim3b

variable {Umod : Type} [AddCommGroup Umod] [Module (ZMod 2) Umod]

theorem NatDec.exists_isMax_proj_ne_bot (D : Data G)
    {ρ : Representation (ZMod 2) (MBar D.M D.U) Umod} {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (d : NatDec ρ (mbarImage D.M D.U (proofN D)) Nb) (i : Fin m) :
    ∃ A' : Subgroup G, CFSG.Quasithin.IsMaxElemAbelian D.T A' ∧
      d.proj i (mbarImage D.M D.U A') ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, y, hy, hne⟩ := NatDec.exists_act_ne D d i
  apply hne
  have hJ : jOf D.T ≤ ((trivSub ρ (natIi ρ (mbarImage D.M D.U (proofN D)) (Nb i))).comap
      (QuotientGroup.mk' (kerAct D.M D.U).normalCore)).map D.M.subtype := by
    refine jOf_le_of_forall_isMax fun A' hA' x hx => ?_
    have hxM : x ∈ D.M := D.sylowM.le (hA'.1 hx)
    have hA'N : A' ≤ proofN D := (le_jOf_of_isMax hA').trans (uc22p22e_jOf_le D.sylowM)
    have hAb : mbarImage D.M D.U A' ≤ mbarImage D.M D.U (proofN D) := mbarImage_mono D.M D.U hA'N
    refine ⟨⟨x, hxM⟩, fun z hz => ?_, rfl⟩
    obtain ⟨b, hb, hbz⟩ := d.exists_proj_act i hAb (a := QuotientGroup.mk' _ ⟨x, hxM⟩)
      ⟨⟨x, hxM⟩, hx, rfl⟩ hz
    rw [hcon A' hA', Subgroup.mem_bot] at hb
    rw [hbz, hb]
    simp
  obtain ⟨w, hw, rfl⟩ := ha
  obtain ⟨w', hw', hww⟩ := hJ hw
  have : w' = w := Subtype.ext hww
  subst this
  exact hw' y hy

theorem bsub_injective_of_le {V : Subgroup G} {Vmod : Type} [AddCommGroup Vmod] [Module (ZMod 2) Vmod]
    (e : ↥V ≃* Multiplicative Vmod) {W W' : Subgroup G} (hW : W ≤ V) (hW' : W' ≤ V)
    (h : bsub e W = bsub e W') : W = W' :=
  le_antisymm ((bsub_le_iff e hW).1 h.le) ((bsub_le_iff e hW').1 h.ge)

theorem exists_isSylow_E (D : Data G) (Ch : Choice2011 G) (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch)
    (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) (i : Fin m) :
    ∃ Q : Subgroup (MBar D.M D.U), CFSG.ABGLocalTools.IsSylowOf 2 Q (Nb i) ∧
      proofEiHat D (preN D (Nb i)) = ⁅proofIi D (preN D (Nb i)), preMbar D Q⁆ := by
  classical
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hV := uc22p22xf_hV D
  obtain ⟨A', hmax, hne⟩ := NatDec.exists_isMax_proj_ne_bot D d i
  have hA'M : A' ≤ D.M := hmax.1.trans D.sylowM.le
  have hA'J := le_jOf_of_isMax hmax
  have hA'N : A' ≤ proofN D := hA'J.trans (uc22p22e_jOf_le D.sylowM)
  have hAb : mbarImage D.M D.U A' ≤ mbarImage D.M D.U (proofN D) :=
    mbarImage_mono D.M D.U hA'N
  have hAbp : IsPGroup 2 (mbarImage D.M D.U A') :=
    ((uc22p22e_isPGroup_of_elem hmax.2.1).comap_subtype (K := D.M)).map _
  have hoff : Nat.card Umod ≤ Nat.card (mbarImage D.M D.U A') *
      Nat.card (fixSub ρ (mbarImage D.M D.U A')) := by
    rw [← relIndex_mul_card_fixSub D e ρ hc hA'M, uc22br4_card_mbarImage D.M D.U _ hV hA'M]
    exact Nat.mul_le_mul_right _
      (uc22p22xf_relIndex_le (uc22p22xf_UleT D) (uc22p22xf_hel D) hmax)
  obtain ⟨-, hsyl⟩ := d.offender_eq hAb hAbp hoff
  have hP : ¬ 2 ∣ (d.proj i (mbarImage D.M D.U A')).relIndex (Nb i) := (hsyl i).resolve_left hne
  have hQbN : mbarImage D.M D.U (jOf D.T) ≤ mbarImage D.M D.U (proofN D) :=
    mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM)
  have hQb2 : IsPGroup 2 (mbarImage D.M D.U (jOf D.T)) :=
    ((D.sylowM.isPGroup.to_le (uc22p22e_jOf_le_self D.T)).comap_subtype (K := D.M)).map _
  have hQi : CFSG.ABGLocalTools.IsSylowOf 2 (d.proj i (mbarImage D.M D.U (jOf D.T))) (Nb i) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨d.proj_le i _, d.isPGroup_proj i hQb2,
      fun hdvd => hP ?_⟩
    exact hdvd.trans (Subgroup.relIndex_dvd_of_le_left (Nb i)
      (d.proj_mono i (mbarImage_mono D.M D.U hA'J)))
  refine ⟨_, hQi, ?_⟩
  have hNiM := preN_le_M D (Nb i)
  have hEU : ⁅proofIi D (preN D (Nb i)), preMbar D (d.proj i (mbarImage D.M D.U (jOf D.T)))⁆ ≤ D.U :=
    commutator_le_of_normalizer (proofIi_le D hNiM) ((preMbar_le_M D _).trans hV)
  have h1 := (bsub_commutator hV e ρ hc (proofIi_le D hNiM) (preMbar_le_M D
    (d.proj i (mbarImage D.M D.U (jOf D.T))))).2
  rw [bsub_proofIi D e ρ hc (d.le i), mbarImage_preMbar] at h1
  have h2 := bsub_proofEiHat D e ρ hc (d.le i)
  rw [d.commOn_proj i hQbN] at h2
  exact bsub_injective_of_le e (proofEiHat_le D hNiM) hEU (h2.trans h1.symm)

end Claim3b

end P22x

open P22x

theorem uc22p22xh_mem_normalizer (D : Data G) {Y Q : Subgroup (MBar D.M D.U)} {y : G} (hy : y ∈ D.M)
    (hyY : (QuotientGroup.mk ⟨y, hy⟩ : MBar D.M D.U) ∈ normalizer (Y : Set (MBar D.M D.U)))
    (hyQ : (QuotientGroup.mk ⟨y, hy⟩ : MBar D.M D.U) ∈ normalizer (Q : Set (MBar D.M D.U))) :
    y ∈ normalizer ((⁅proofIi D (preN D Y), preMbar D Q⁆ : Subgroup G) : Set G) := by
  have hU : y ∈ normalizer (D.U : Set G) := uc22p22xf_hV D hy
  have hN : y ∈ normalizer ((proofN D : Subgroup G) : Set G) := uc22p22t_M_le_normalizer_jOf D hy
  have hNi : y ∈ normalizer ((preN D Y : Subgroup G) : Set G) :=
    mem_normalizer_inf hN (mem_normalizer_preMbar D hy hyY)
  exact mem_normalizer_commutator (mem_normalizer_commutator (mem_normalizer_commutator hU hN) hNi)
    (mem_normalizer_preMbar D hy hyQ)

theorem uc22p22xh_conj (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (i : Fin m)
    (Q : Sylow 2 ↥(Nb i)) :
    ∃ n ∈ preN D (Nb i),
      ⁅proofIi D (preN D (Nb i)), preMbar D ((Q : Subgroup ↥(Nb i)).map (Nb i).subtype)⁆ =
        (proofEiHat D (preN D (Nb i))).map (MulAut.conj n).toMonoidHom := by
  classical
  obtain ⟨Q₁, hQ₁, hE⟩ := exists_isSylow_E D Ch h3 h51 hH c hNb i
  have hQ' : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup ↥(Nb i)).map (Nb i).subtype) (Nb i) :=
    ⟨Q, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hQ₁.exists_mem_conj hQ'
  have hkN : k ∈ mbarImage D.M D.U (proofN D) := (le_iSup Nb i).trans hNb.1.1.le hk
  obtain ⟨z, hz, rfl⟩ := hkN
  have hnM : (z : G) ∈ D.M := z.2
  have hn : (z : G) ∈ preN D (Nb i) := (mem_preN D).2 ⟨hz, hnM, hk⟩
  refine ⟨(z : G), hn, ?_⟩
  set Q' : Subgroup (MBar D.M D.U) := (Q : Subgroup ↥(Nb i)).map (Nb i).subtype with hQ'def
  have hpre : preMbar D Q' = (preMbar D Q₁).map (MulAut.conj (z : G)).toMonoidHom := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxM, hxQ⟩ := (mem_preMbar D).1 hx
      have h1 := (hconj _).1 hxQ
      refine ⟨(z : G)⁻¹ * x * (z : G), (mem_preMbar D).2 ⟨?_, ?_⟩, by simp [mul_assoc]⟩
      · have := D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hnM) hxM) hnM
        exact this
      · exact h1
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hpM, hpQ⟩ := (mem_preMbar D).1 hp
      refine (mem_preMbar D).2 ⟨?_, ?_⟩
      · exact D.M.mul_mem (D.M.mul_mem hnM hpM) (D.M.inv_mem hnM)
      · refine (hconj _).2 ?_
        have e : (QuotientGroup.mk z : MBar D.M D.U)⁻¹ *
            (QuotientGroup.mk ⟨(z : G) * p * (z : G)⁻¹,
              D.M.mul_mem (D.M.mul_mem hnM hpM) (D.M.inv_mem hnM)⟩ : MBar D.M D.U) *
              QuotientGroup.mk z = (QuotientGroup.mk ⟨p, hpM⟩ : MBar D.M D.U) := by
          rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          apply Subtype.ext
          simp [mul_assoc]
        show (QuotientGroup.mk z : MBar D.M D.U)⁻¹ *
            (QuotientGroup.mk ⟨(z : G) * p * (z : G)⁻¹, _⟩ : MBar D.M D.U) *
              QuotientGroup.mk z ∈ Q₁
        rw [e]
        exact hpQ
  have hV := uc22p22xf_hV D
  have hU : (z : G) ∈ normalizer (D.U : Set G) := hV hnM
  have hN : (z : G) ∈ normalizer ((proofN D : Subgroup G) : Set G) :=
    uc22p22t_M_le_normalizer_jOf D hnM
  have hI : (z : G) ∈ normalizer ((proofIi D (preN D (Nb i)) : Subgroup G) : Set G) :=
    mem_normalizer_commutator (mem_normalizer_commutator hU hN) (Subgroup.le_normalizer hn)
  rw [hE, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hI, ← hpre]

end CFSG.LocalAnalysis.UniquenessCase.UC22
