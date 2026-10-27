module

public import CFSG.Quasithin.Background.F918Z8b
public import CFSG.GroupTheory.SupCommute
public import CFSG.LargeExtraspecial.S12Seven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Aux
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9ProdA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s1611e3_c6_alt_simpleCentreless {X : Type} [Group X] [Finite X]
    (h : IsAlt X 5) :
    CFSG.ComponentClassification.AutL2Facts.SimpleCentreless X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup X := e.isSimpleGroup
  have hcardX : Nat.card X = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hcomm : ∀ a b : X, a * b = b * a := fun a b => hc a b
    haveI : IsMulCommutative X := ⟨⟨hcomm⟩⟩
    have hprime : Nat.Prime (Nat.card X) :=
      Group.is_simple_iff_prime_card.mp (show IsSimpleGroup X from inferInstance)
    rw [hcardX] at hprime
    exact (by norm_num at hprime : False)
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨fun N _ => IsSimpleGroup.eq_bot_or_eq_top_of_normal N, fun z hz => ?_,
    ⟨a, ?_⟩⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h0 | h0
    · have hz' : z ∈ Subgroup.center X :=
        Subgroup.mem_center_iff.mpr fun g => (hz g).symm
      rwa [h0, Subgroup.mem_bot] at hz'
    · have ha : a ∈ Subgroup.center X := h0 ▸ Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab
  · rintro rfl
    exact hab (by rw [one_mul, mul_one])

private theorem s1611e3_c6_alt_perfect {X : Type} [Group X] (h : IsAlt X 5) :
    Group.IsPerfect X := by
  obtain ⟨e⟩ := h
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem s1611e3_c6_altNat_map {T : Type} [CommGroup T] (x : MulAut T)
    {H : Subgroup (MulAut T)} {U : Subgroup T} {n : ℕ}
    (h : AlternatingNatural H U ⊥ n) :
    AlternatingNatural (H.map (MulAut.conj x).toMonoidHom) (U.map x.toMonoidHom) ⊥ n := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨_, by
    simpa only [conjAutSub, Subgroup.map_bot] using d321b_realizes_map x hπ⟩

private theorem s1611e3_c6_sumOfNat_map {T : Type} [CommGroup T] (x : MulAut T)
    {N : Subgroup (MulAut T) → Subgroup T → Subgroup T → Prop}
    (hN : ∀ H U, N H U ⊥ →
      N (H.map (MulAut.conj x).toMonoidHom) (U.map x.toMonoidHom) ⊥)
    {H : Subgroup (MulAut T)} {U : Subgroup T} {k : ℕ}
    (h : SumOfNat N H U ⊥ k) :
    SumOfNat N (H.map (MulAut.conj x).toMonoidHom) (U.map x.toMonoidHom) ⊥ k := by
  obtain ⟨I, -, hind, hsup, hnat⟩ := h
  refine ⟨fun i => (I i).map x.toMonoidHom, fun i => bot_le, ?_, ?_,
    fun i => hN _ _ (hnat i)⟩
  · intro i
    have hle := Subgroup.map_mono (f := x.toMonoidHom) (hind i)
    rw [Subgroup.map_inf_eq _ _ x.toMonoidHom x.injective, Subgroup.map_sup,
      Subgroup.map_bot] at hle
    simp only [Subgroup.map_iSup x.toMonoidHom] at hle
    simpa using hle
  · have h := congrArg (fun V : Subgroup T => V.map x.toMonoidHom) hsup
    rwa [Subgroup.map_sup, Subgroup.map_bot, Subgroup.map_iSup x.toMonoidHom] at h

private theorem s1611e3_c6_alt_transport {T : Type} [CommGroup T] (x : MulAut T)
    {A : Subgroup (MulAut T)} {W : Subgroup T}
    (hAlt : IsAlt ↥A 5)
    (hSum : SumOfNat (fun H U Z => AlternatingNatural H U Z 5) A W ⊥ 2) :
    IsAlt ↥(A.map (MulAut.conj x).toMonoidHom) 5 ∧
      SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
        (A.map (MulAut.conj x).toMonoidHom) (W.map x.toMonoidHom) ⊥ 2 := by
  constructor
  · obtain ⟨eA⟩ := hAlt
    exact ⟨(Subgroup.equivMapOfInjective A (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective).symm.trans eA⟩
  · exact s1611e3_c6_sumOfNat_map x (fun _ _ h => s1611e3_c6_altNat_map x h) hSum

private theorem s1611e3_c6_v1 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h6 : Case168_6 D V₀ V hV L) : v1Sub D.M V₀ V hV L = V₀ := by
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    refine s1611e3_v1Sub_eq_bot_of_fix D hV (fun w hw hfix => ?_)
    have hwfix : w ∈ fixV (lBar ⊥ V hV L) := by
      rw [mem_fixV]
      intro l hl
      exact hfix l hl
    have hbot : wTil (⊥ : Subgroup G) V hV L ⊓ fixV (lBar ⊥ V hV L) = ⊥ := by
      rcases h6.2.1 with ⟨-, hSum⟩ | ⟨-, hSum⟩
      · exact s16e_inf_fixV_eq_bot_sumOfNat_alt (n := 5) (by norm_num) (by norm_num) hSum
      · exact s16c167_inf_fixV_eq_bot_of_sumOfNat (n := 3) (by norm_num) hSum
    have : w ∈ wTil (⊥ : Subgroup G) V hV L ⊓ fixV (lBar ⊥ V hV L) := ⟨hw, hwfix⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  · exact v1Sub_of_ne_bot D.M V₀ V hV L hV0

private theorem s1611e3_c6_structure {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) {g : MulAut (Vtil V₀ V hV)}
    (hg : S16n9bTwo (Mbar D.M V₀ V hV) (lBar V₀ V hV L) g)
    (hperfA : Group.IsPerfect ↥(lBar V₀ V hV L))
    (hcenterA : ∀ z : ↥(lBar V₀ V hV L), (∀ w, z * w = w * z) → z = 1)
    (hAF : lBar V₀ V hV L ≤ Fstar (Mbar D.M V₀ V hV))
    (e : ↥(Fstar (Mbar D.M V₀ V hV)) ≃*
      (Multiplicative (ZMod 3) × ↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L))) :
    ∃ (x : MulAut (Vtil V₀ V hV)) (Z : Subgroup (MulAut (Vtil V₀ V hV))),
      x ∈ barSub V₀ V hV D.T ∧
      (∀ a ∈ lBar V₀ V hV L, ∀ b ∈ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom,
        a * b = b * a) ∧
      lBar V₀ V hV L ⊓ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom = ⊥ ∧
      (commutator ↥(Fstar (Mbar D.M V₀ V hV))).map (Fstar (Mbar D.M V₀ V hV)).subtype =
        lBar V₀ V hV L ⊔ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom ∧
      (∀ b ∈ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom, ∀ w ∈ wTil V₀ V hV L,
        b w = w) ∧
      (∀ a ∈ lBar V₀ V hV L, ∀ w ∈ (wTil V₀ V hV L).map x.toMonoidHom, a w = w) ∧
      wTil V₀ V hV L ⊓ (wTil V₀ V hV L).map x.toMonoidHom = ⊥ ∧
      wTil V₀ V hV L ⊔ (wTil V₀ V hV L).map x.toMonoidHom = ⊤ ∧
      IsSylowIn 2 (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) (lBar V₀ V hV L) ∧
      Nat.card ↥Z = 3 ∧ Z ≤ Mbar D.M V₀ V hV ∧
      (∀ m ∈ Mbar D.M V₀ V hV, Z.map (MulAut.conj m).toMonoidHom = Z) ∧
      (∀ z ∈ Z, ∀ l ∈ lBar V₀ V hV L, z * l = l * z) ∧
      (∀ z ∈ Z, ∀ w ∈ wTil V₀ V hV L, z w ∈ wTil V₀ V hV L) ∧
      (∀ z ∈ Z, z ≠ 1 → ∃ w ∈ wTil V₀ V hV L, z w ≠ w) ∧
      Fstar (Mbar D.M V₀ V hV) = Z ⊔ (lBar V₀ V hV L ⊔ (lBar V₀ V hV L).map
        (MulAut.conj x).toMonoidHom) ∧
      Z ⊓ (lBar V₀ V hV L ⊔ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom) = ⊥ ∧
      (∀ z ∈ Z, ∀ l ∈ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom, z * l = l * z) ∧
      (∀ z ∈ Z, ∀ w ∈ (wTil V₀ V hV L).map x.toMonoidHom,
        z w ∈ (wTil V₀ V hV L).map x.toMonoidHom) ∧
      (∀ z ∈ Z, z ≠ 1 → ∃ w ∈ (wTil V₀ V hV L).map x.toMonoidHom, z w ≠ w) ∧
      (∀ φ ∈ Mbar D.M V₀ V hV,
        ((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom = lBar V₀ V hV L ∧
          ((lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
            (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom ∧
          (wTil V₀ V hV L).map φ.toMonoidHom = wTil V₀ V hV L ∧
          ((wTil V₀ V hV L).map x.toMonoidHom).map φ.toMonoidHom =
            (wTil V₀ V hV L).map x.toMonoidHom) ∨
        ((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom =
            (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom ∧
          ((lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
            lBar V₀ V hV L ∧
          (wTil V₀ V hV L).map φ.toMonoidHom = (wTil V₀ V hV L).map x.toMonoidHom ∧
          ((wTil V₀ V hV L).map x.toMonoidHom).map φ.toMonoidHom = wTil V₀ V hV L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L with hA
  set Tb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV D.T with hTb
  set Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hMb
  set F : Subgroup (MulAut (Vtil V₀ V hV)) := Fstar (Mbar D.M V₀ V hV) with hF
  set E : Subgroup (MulAut (Vtil V₀ V hV)) := (commutator ↥F).map F.subtype with hE
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hc.setting.hyp151.hyp125.pairFacts.le_normalizer
      hc.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hTsyl : IsSylowIn 2 Tb Mb :=
    s1611e3_barSub_sylow hMstab (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM)
  have huniq : ∀ a ∈ Mb, ∀ b ∈ Mb, A.map (MulAut.conj a).toMonoidHom ≠ A →
      A.map (MulAut.conj b).toMonoidHom ≠ A →
      A.map (MulAut.conj a).toMonoidHom = A.map (MulAut.conj b).toMonoidHom := by
    intro a ha b hb hane hbne
    rcases hg.conj a ha with hh | hh
    · exact absurd hh hane
    · rcases hg.conj b hb with hh' | hh'
      · exact absurd hh' hbne
      · rw [hh, hh']
  have hx_exists : ∃ x ∈ Tb, A.map (MulAut.conj x).toMonoidHom ≠ A := by
    by_contra hcon
    have hstab : Tb ≤ Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV))) := by
      intro φ hφ
      refine ⟨hTsyl.le hφ, ?_⟩
      exact (Subgroup.mem_normalizer_iff_map_conj_eq (H := A) (g := φ)).mpr (by
        by_contra hne
        exact hcon ⟨φ, hφ, hne⟩)
    have hidx : ((Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))).subgroupOf
        Mb).index = 2 :=
      s1611e3_relIndex_stabilizer_eq_two (K := A) (x₁ := g) hg.mem hg.ne huniq
    have hrel : Tb.relIndex (Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))) *
        (Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))).relIndex Mb =
          Tb.relIndex Mb :=
      Subgroup.relIndex_mul_relIndex Tb
        (Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))) Mb hstab inf_le_left
    have hdvd : 2 ∣ Tb.relIndex Mb := by
      rw [← hrel]
      have h2 : (Mb ⊓ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV)))).relIndex Mb = 2 :=
        hidx
      rw [h2]
      exact dvd_mul_left 2 _
    exact hTsyl.not_dvd_relIndex hdvd
  obtain ⟨x, hxTb, hxAne⟩ := hx_exists
  have hxMb : x ∈ Mb := hTsyl.le hxTb
  have hAx : A.map (MulAut.conj x).toMonoidHom = A.map (MulAut.conj g).toMonoidHom := by
    rcases hg.conj x hxMb with hh | hh
    · exact absurd hh hxAne
    · exact hh
  have hAcenter : Subgroup.center ↥A = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    exact hcenterA z fun w => (Subgroup.mem_center_iff.mp hz w).symm
  have hAinf : A ⊓ A.map (MulAut.conj x).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hycenter : (⟨y, hy.1⟩ : ↥A) ∈ Subgroup.center ↥A := by
      rw [Subgroup.mem_center_iff]
      intro gg
      apply Subtype.ext
      have hgy : y ∈ A.map (MulAut.conj g).toMonoidHom := by rw [← hAx]; exact hy.2
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hg.comm
      have hcy : y * (gg : MulAut (Vtil V₀ V hV)) =
          (gg : MulAut (Vtil V₀ V hV)) * y :=
        Subgroup.mem_centralizer_iff.mp (hle gg.2) y hgy
      simpa using hcy.symm
    rw [hAcenter, Subgroup.mem_bot] at hycenter
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hycenter
  obtain ⟨hFX, hFn, hselfF⟩ := s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)
  have hEcard : Nat.card ↥E = Nat.card ↥A * Nat.card ↥A := by
    show Nat.card ↥((commutator ↥F).map F.subtype) = Nat.card ↥A * Nat.card ↥A
    rw [Subgroup.card_map_of_injective (f := F.subtype) F.subtype_injective,
      s1611e3_commutator_card (F := ↥F) (Z := Multiplicative (ZMod 3)) (S := ↥A) hperfA e]
  have hEeq : E = ⁅F, F⁆ := Subgroup.map_subtype_commutator F
  have hAperf : ⁅A, A⁆ = A := by
    haveI : Group.IsPerfect ↥A := hperfA
    exact Subgroup.commutator_eq_self
  have hA'perf : ⁅A.map (MulAut.conj x).toMonoidHom, A.map (MulAut.conj x).toMonoidHom⁆ =
      A.map (MulAut.conj x).toMonoidHom := by
    haveI : Group.IsPerfect ↥A := hperfA
    haveI : Group.IsPerfect ↥(A.map (MulAut.conj x).toMonoidHom) :=
      Group.IsPerfect.map (f := (MulAut.conj x).toMonoidHom)
    exact Subgroup.commutator_eq_self
  have hAE : A ≤ E := by
    rw [hEeq]
    calc A = ⁅A, A⁆ := hAperf.symm
      _ ≤ ⁅F, F⁆ := Subgroup.commutator_mono hAF hAF
  have hA'F : A.map (MulAut.conj x).toMonoidHom ≤ F := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    simpa [MulAut.conj_apply] using hFn x hxMb a (hAF ha)
  have hA'E : A.map (MulAut.conj x).toMonoidHom ≤ E := by
    rw [hEeq]
    calc A.map (MulAut.conj x).toMonoidHom
        = ⁅A.map (MulAut.conj x).toMonoidHom, A.map (MulAut.conj x).toMonoidHom⁆ :=
          hA'perf.symm
      _ ≤ ⁅F, F⁆ := Subgroup.commutator_mono hA'F hA'F
  have hcomm : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj x).toMonoidHom, a * b = b * a := by
    intro a ha b hb
    rw [hAx] at hb
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hg.comm
    exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  have hAsup_card : Nat.card ↥(A ⊔ A.map (MulAut.conj x).toMonoidHom) =
      Nat.card ↥A * Nat.card ↥A := by
    rw [CFSG.card_sup_eq_mul_of_commute A (A.map (MulAut.conj x).toMonoidHom)
      (fun a ha b hb => hcomm a ha b hb) hAinf,
      Subgroup.card_map_of_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective]
  have hE_eq : E = A ⊔ A.map (MulAut.conj x).toMonoidHom := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (sup_le hAE hA'E) ?_
    rw [hEcard, hAsup_card]
  have hEMb : E ≤ Mb := by
    rw [hEeq]
    exact (Subgroup.commutator_le_self F).trans hFX
  have hEnorm : (E.subgroupOf Mb).Normal :=
    (Subgroup.normal_subgroupOf_iff hEMb).2 fun hh k hhk hk =>
      s1611e3_commutator_conj_mem hFn k hk hh hhk
  have hA'norm : A.map (MulAut.conj x).toMonoidHom ≤
      Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV))) := by
    have hle : A.map (MulAut.conj x).toMonoidHom ≤
        Subgroup.centralizer (A : Set (MulAut (Vtil V₀ V hV))) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      rw [Subgroup.commutator_comm, hAx]
      exact hg.comm
    exact hle.trans (Subgroup.centralizer_le_normalizer (A : Set (MulAut (Vtil V₀ V hV))))
  have hEnormA : E ≤ Subgroup.normalizer (A : Set (MulAut (Vtil V₀ V hV))) := by
    rw [hE_eq]
    exact sup_le Subgroup.le_normalizer hA'norm
  have hAnormE : (A.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).2 hEnormA
  have hTEsyl : IsSylowIn 2 (Tb ⊓ E) E := IsSylowIn.inf_normal hTsyl hEMb hEnorm
  have hTEAsyl : IsSylowIn 2 ((Tb ⊓ E) ⊓ A) A := IsSylowIn.inf_normal hTEsyl hAE hAnormE
  have hsyl : IsSylowIn 2 (Tb ⊓ A) A := by
    simpa [inf_assoc, inf_eq_right.mpr hAE] using hTEAsyl
  have hWmap : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom =
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map g.toMonoidHom := by
    rw [← s15_Infra_commSub_top_map_conj A x, ← s15_Infra_commSub_top_map_conj A g, hAx]
  have hfixB : ∀ b ∈ A.map (MulAut.conj x).toMonoidHom, ∀ w ∈ wTil V₀ V hV L,
      b w = w := by
    intro b hb w hw
    rw [hAx] at hb
    have hw' : w ∈ commSub (⊤ : Subgroup (Vtil V₀ V hV)) A := by
      simpa [wTil, hA, lBar] using hw
    exact hg.fixB b hb w hw'
  have hfixA : ∀ a ∈ A, ∀ w ∈ (wTil V₀ V hV L).map x.toMonoidHom, a w = w := by
    intro a ha w hw
    have hw1 : w ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom := by
      simpa [wTil, hA, lBar] using hw
    have hw' : w ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map g.toMonoidHom := by
      rwa [hWmap] at hw1
    exact hg.fixA a ha w hw'
  have hWinf : wTil V₀ V hV L ⊓ (wTil V₀ V hV L).map x.toMonoidHom = ⊥ := by
    show commSub (⊤ : Subgroup (Vtil V₀ V hV)) A ⊓
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom = ⊥
    rw [hWmap]
    exact hg.inf
  have hWsup : wTil V₀ V hV L ⊔ (wTil V₀ V hV L).map x.toMonoidHom = ⊤ := by
    show commSub (⊤ : Subgroup (Vtil V₀ V hV)) A ⊔
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom = ⊤
    rw [hWmap]
    exact hg.sup
  set Z : Subgroup (MulAut (Vtil V₀ V hV)) :=
    (Subgroup.center ↥F).map F.subtype with hZ
  have hZcard : Nat.card ↥Z = 3 := by
    show Nat.card ↥((Subgroup.center ↥F).map F.subtype) = 3
    rw [s16c167_frame_centerF_card (F := F) (Z := Multiplicative (ZMod 3)) hcenterA e,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hZconj := s16c167_frame_centerF_conj (X := Mb) (F := F) hFn
  have hZX : Z ≤ Mb := fun z hz => hFX ((s16c167_frame_mem_centerF.1 hz).1)
  have hZL : ∀ z ∈ Z, ∀ l ∈ A, z * l = l * z := fun z hz l hl =>
    (s16c167_frame_mem_centerF.1 hz).2 l (hAF hl)
  have hZstab : ∀ z ∈ Z, ∀ w ∈ commSub (⊤ : Subgroup (Vtil V₀ V hV)) A,
      z w ∈ commSub (⊤ : Subgroup (Vtil V₀ V hV)) A := by
    intro z hz w hw
    refine commSub_top_stable151b (X := A) (g := z) (fun x hx => ?_) w hw
    have h1 : x * z = z * x := ((s16c167_frame_mem_centerF.1 hz).2 x (hAF hx)).symm
    rw [show z * x * z⁻¹ = x by rw [← h1]; group]
    exact hx
  have hWconj : {Y : Subgroup (Vtil V₀ V hV) |
      ∃ φ ∈ Mb, Y = (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map φ.toMonoidHom} =
      {(commSub (⊤ : Subgroup (Vtil V₀ V hV)) A),
        (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map g.toMonoidHom} := by
    ext Y
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      rw [← s15_Infra_commSub_top_map_conj A φ]
      rcases hg.conj φ hφ with h | h
      · rw [h]; simp
      · rw [h, s15_Infra_commSub_top_map_conj A g]; simp
    · rintro (rfl | rfl)
      · refine ⟨1, Mb.one_mem, ?_⟩
        ext y
        simp
      · exact ⟨g, hg.mem, rfl⟩
  have hWframe_sup : sSup {Y : Subgroup (Vtil V₀ V hV) |
      ∃ φ ∈ Mb, Y = (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map φ.toMonoidHom} = ⊤ := by
    rw [hWconj, sSup_pair]
    exact hg.sup
  have hZf : ∀ z ∈ Z, z ≠ 1 →
      ∃ w ∈ commSub (⊤ : Subgroup (Vtil V₀ V hV)) A, z w ≠ w :=
    s16c167_frame_faithful_of_conj_sup (W := Vtil V₀ V hV) (X := Mb)
      (U := commSub (⊤ : Subgroup (Vtil V₀ V hV)) A) (p := 3) (by norm_num) hZcard hZconj
      hWframe_sup
  obtain ⟨hcs, hci⟩ := s16c167_frame_center_sup_commutator hperfA hcenterA e
  have htopmap : (⊤ : Subgroup ↥F).map F.subtype = F := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      exact z.2
    · intro hy
      exact ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  have hFsupZ : F = Z ⊔ E := by
    have h := congrArg (fun X : Subgroup ↥F => X.map F.subtype) hcs
    rw [Subgroup.map_sup, htopmap] at h
    exact h.symm
  have hZinfE : Z ⊓ E = ⊥ := by
    have h := congrArg (fun X : Subgroup ↥F => X.map F.subtype) hci
    rwa [Subgroup.map_inf_eq _ _ _ F.subtype_injective, Subgroup.map_bot] at h
  have hZcenA' : ∀ z ∈ Z, ∀ l ∈ A.map (MulAut.conj x).toMonoidHom, z * l = l * z :=
    fun z hz l hl => (s16c167_frame_mem_centerF.1 hz).2 l (hA'F hl)
  have hZstabA' : ∀ z ∈ Z, ∀ w ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map
      x.toMonoidHom, z w ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom := by
    intro z hz w hw
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hw
    have hxinvZ : (MulAut.conj x⁻¹).toMonoidHom z ∈ Z := by
      have hmem : (MulAut.conj x⁻¹).toMonoidHom z ∈ Z.map (MulAut.conj x⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hz
      rwa [hZconj x⁻¹ (Mb.inv_mem hxMb)] at hmem
    have h1 : z ((MulEquiv.toMonoidHom x) u) =
        (MulEquiv.toMonoidHom x) (((MulAut.conj x⁻¹).toMonoidHom z) u) := by
      simp [MulAut.mul_apply]
    rw [h1]
    exact Subgroup.mem_map.2 ⟨((MulAut.conj x⁻¹).toMonoidHom z) u,
      hZstab ((MulAut.conj x⁻¹).toMonoidHom z) hxinvZ u hu, rfl⟩
  have hZfA' : ∀ z ∈ Z, z ≠ 1 →
      ∃ w ∈ (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom, z w ≠ w := by
    intro z hz hz1
    have hxinvZ : (MulAut.conj x⁻¹).toMonoidHom z ∈ Z := by
      have hmem : (MulAut.conj x⁻¹).toMonoidHom z ∈ Z.map (MulAut.conj x⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hz
      rwa [hZconj x⁻¹ (Mb.inv_mem hxMb)] at hmem
    obtain ⟨u, hu, hune⟩ := hZf ((MulAut.conj x⁻¹).toMonoidHom z) hxinvZ (by
      intro hconj
      apply hz1
      calc z = x * ((MulAut.conj x⁻¹).toMonoidHom z) * x⁻¹ := by
            simp [MulAut.conj_apply]; group
        _ = x * 1 * x⁻¹ := by rw [hconj]
        _ = 1 := by group)
    refine ⟨x u, Subgroup.mem_map.2 ⟨u, hu, rfl⟩, ?_⟩
    intro hfix
    apply hune
    have h := congrArg (fun w => x⁻¹ w) hfix
    simpa [MulAut.mul_apply] using h
  have hphi : ∀ φ ∈ Mb,
      ((A.map (MulAut.conj φ).toMonoidHom = A ∧
          (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
            A.map (MulAut.conj x).toMonoidHom ∧
          (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map φ.toMonoidHom =
            commSub (⊤ : Subgroup (Vtil V₀ V hV)) A ∧
          ((commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom).map φ.toMonoidHom =
            (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom) ∨
        (A.map (MulAut.conj φ).toMonoidHom = A.map (MulAut.conj x).toMonoidHom ∧
          (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom = A ∧
          (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map φ.toMonoidHom =
            (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom ∧
          ((commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom).map φ.toMonoidHom =
            commSub (⊤ : Subgroup (Vtil V₀ V hV)) A)) := by
    intro φ hφ
    have hmem : A.map (MulAut.conj φ).toMonoidHom = A ∨
        A.map (MulAut.conj φ).toMonoidHom = A.map (MulAut.conj x).toMonoidHom := by
      have h := hg.conj φ hφ
      rw [← hAx] at h
      exact h
    have hAxφmem : (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom = A ∨
        (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
          A.map (MulAut.conj x).toMonoidHom := by
      rw [s1611e3_nine_map_conj_map_conj]
      have h := hg.conj (φ * x) (Mb.mul_mem hφ hxMb)
      rwa [← hAx] at h
    rcases hmem with hφA | hφA
    · have hAxφ : (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
          A.map (MulAut.conj x).toMonoidHom := by
        rcases hAxφmem with h1 | h1
        · exfalso
          have h2 : (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
              A.map (MulAut.conj φ).toMonoidHom := by rw [h1, hφA]
          exact hxAne (Subgroup.map_injective (MulAut.conj φ).injective h2)
        · exact h1
      have hWφ : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map φ.toMonoidHom =
          commSub (⊤ : Subgroup (Vtil V₀ V hV)) A := by
        rw [← s15_Infra_commSub_top_map_conj A φ, hφA]
      have hWxφ : ((commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom).map
          φ.toMonoidHom = (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom := by
        rw [← s15_Infra_commSub_top_map_conj A x,
          ← s15_Infra_commSub_top_map_conj (A.map (MulAut.conj x).toMonoidHom) φ, hAxφ]
      exact Or.inl ⟨hφA, hAxφ, hWφ, hWxφ⟩
    · have hAxφ : (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom = A := by
        rcases hAxφmem with h1 | h1
        · exact h1
        · exfalso
          have h2 : (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
              A.map (MulAut.conj φ).toMonoidHom := by rw [h1, hφA]
          exact hxAne (Subgroup.map_injective (MulAut.conj φ).injective h2)
      have hWφ : (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map φ.toMonoidHom =
          (commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom := by
        rw [← s15_Infra_commSub_top_map_conj A φ, hφA,
          ← s15_Infra_commSub_top_map_conj A x]
      have hWxφ : ((commSub (⊤ : Subgroup (Vtil V₀ V hV)) A).map x.toMonoidHom).map
          φ.toMonoidHom = commSub (⊤ : Subgroup (Vtil V₀ V hV)) A := by
        rw [← s15_Infra_commSub_top_map_conj A x,
          ← s15_Infra_commSub_top_map_conj (A.map (MulAut.conj x).toMonoidHom) φ, hAxφ]
      exact Or.inr ⟨hφA, hAxφ, hWφ, hWxφ⟩
  refine ⟨x, Z, hxTb, hcomm, hAinf, ?_, hfixB, hfixA, hWinf, hWsup, hsyl, hZcard, hZX,
    hZconj, hZL, hZstab, hZf, ?_, ?_, hZcenA', hZstabA', hZfA', hphi⟩
  · show (commutator ↥F).map F.subtype = _
    exact hE_eq
  · show F = _
    rw [hFsupZ, hE_eq]
  · show Z ⊓ _ = ⊥
    rw [← hE_eq, hZinfE]

theorem s1611e3_case6_prod {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h6 : Case168_6 D V₀ V hV L) :
    ∃ (x : MulAut (Vtil V₀ V hV)) (Z : Subgroup (MulAut (Vtil V₀ V hV))),
      x ∈ barSub V₀ V hV D.T ∧
      (∀ a ∈ lBar V₀ V hV L, ∀ b ∈ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom,
        a * b = b * a) ∧
      lBar V₀ V hV L ⊓ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom = ⊥ ∧
      (commutator ↥(Fstar (Mbar D.M V₀ V hV))).map (Fstar (Mbar D.M V₀ V hV)).subtype =
        lBar V₀ V hV L ⊔ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom ∧
      (∀ b ∈ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom, ∀ w ∈ wTil V₀ V hV L,
        b w = w) ∧
      (∀ a ∈ lBar V₀ V hV L, ∀ w ∈ (wTil V₀ V hV L).map x.toMonoidHom, a w = w) ∧
      wTil V₀ V hV L ⊓ (wTil V₀ V hV L).map x.toMonoidHom = ⊥ ∧
      wTil V₀ V hV L ⊔ (wTil V₀ V hV L).map x.toMonoidHom = ⊤ ∧
      IsSylowIn 2 (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) (lBar V₀ V hV L) ∧
      Nat.card ↥Z = 3 ∧ Z ≤ Mbar D.M V₀ V hV ∧
      (∀ m ∈ Mbar D.M V₀ V hV, Z.map (MulAut.conj m).toMonoidHom = Z) ∧
      (∀ z ∈ Z, ∀ l ∈ lBar V₀ V hV L, z * l = l * z) ∧
      (∀ z ∈ Z, ∀ w ∈ wTil V₀ V hV L, z w ∈ wTil V₀ V hV L) ∧
      (∀ z ∈ Z, z ≠ 1 → ∃ w ∈ wTil V₀ V hV L, z w ≠ w) ∧
      Fstar (Mbar D.M V₀ V hV) = Z ⊔ (lBar V₀ V hV L ⊔ (lBar V₀ V hV L).map
        (MulAut.conj x).toMonoidHom) ∧
      Z ⊓ (lBar V₀ V hV L ⊔ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom) = ⊥ ∧
      (∀ z ∈ Z, ∀ l ∈ (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom, z * l = l * z) ∧
      (∀ z ∈ Z, ∀ w ∈ (wTil V₀ V hV L).map x.toMonoidHom,
        z w ∈ (wTil V₀ V hV L).map x.toMonoidHom) ∧
      (∀ z ∈ Z, z ≠ 1 → ∃ w ∈ (wTil V₀ V hV L).map x.toMonoidHom, z w ≠ w) ∧
      (∀ φ ∈ Mbar D.M V₀ V hV,
        ((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom = lBar V₀ V hV L ∧
          ((lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
            (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom ∧
          (wTil V₀ V hV L).map φ.toMonoidHom = wTil V₀ V hV L ∧
          ((wTil V₀ V hV L).map x.toMonoidHom).map φ.toMonoidHom =
            (wTil V₀ V hV L).map x.toMonoidHom) ∨
        ((lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom =
            (lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom ∧
          ((lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj φ).toMonoidHom =
            lBar V₀ V hV L ∧
          (wTil V₀ V hV L).map φ.toMonoidHom = (wTil V₀ V hV L).map x.toMonoidHom ∧
          ((wTil V₀ V hV L).map x.toMonoidHom).map φ.toMonoidHom = wTil V₀ V hV L)) ∧
      (UC22.IsAlt ↥(lBar V₀ V hV L) 5 →
        UC22.IsAlt ↥((lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom) 5 ∧
          SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
            ((lBar V₀ V hV L).map (MulAut.conj x).toMonoidHom)
            ((wTil V₀ V hV L).map x.toMonoidHom) ⊥ 2) := by
  classical
  have h6c := h6
  obtain ⟨⟨e⟩, hfam, hs15, -⟩ := h6
  rcases hfam with ⟨hAlt, hSumAlt⟩ | ⟨hL3, hSumL3⟩
  · haveI : Group.IsSolvable
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 5))) :=
      (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (Or.inl rfl)).1
    have hAltc := hAlt
    have hSC := s1611e3_c6_alt_simpleCentreless (X := ↥(lBar V₀ V hV L)) hAlt
    have hperfA := s1611e3_c6_alt_perfect hAlt
    obtain ⟨eA⟩ := hAlt
    have hout : Group.IsSolvable
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(lBar V₀ V hV L)) :=
      CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv eA.symm
    obtain ⟨hFX, hFn, hselfF⟩ := s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)
    have hLX : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
      barSub_mono V₀ V hV hc.setting.hyp151.le
    have hAF : lBar V₀ V hV L ≤ Fstar (Mbar D.M V₀ V hV) :=
      s16c167_frame_le_of_perfect hFX hLX hFn hselfF
        (s16c167_frame_outer_cyclic_square_solvable hSC hperfA hout e) hperfA
    obtain ⟨g, hg⟩ := s16e_twoConj D h.h1217 hV hc.setting hc.ne_bot
      (s1611e3_c6_v1 h6c) hs15
    obtain ⟨x, Z, h1, h2, h3, h4, h5, h6', h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
      h17, h18, h19, h20, h21⟩ :=
      s1611e3_c6_structure hc hg hperfA (fun z hz => hSC.center z hz) hAF e
    refine ⟨x, Z, h1, h2, h3, h4, h5, h6', h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
      h17, h18, h19, h20, h21, ?_⟩
    intro _
    exact s1611e3_c6_alt_transport x hAltc hSumAlt
  · have hPSL := s16c167_isPSL_of_isL3 hL3
    have hSC := s16c167_isPSL_simpleCentreless hPSL
    have hperfA := s16c167_isPSL_isPerfect hPSL
    have hout : Group.IsSolvable
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥(lBar V₀ V hV L)) :=
      s16c167_isPSL_outer_solvable hPSL
    obtain ⟨hFX, hFn, hselfF⟩ := s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)
    have hLX : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
      barSub_mono V₀ V hV hc.setting.hyp151.le
    have hAF : lBar V₀ V hV L ≤ Fstar (Mbar D.M V₀ V hV) :=
      s16c167_frame_le_of_perfect hFX hLX hFn hselfF
        (s16c167_frame_outer_cyclic_square_solvable hSC hperfA hout e) hperfA
    obtain ⟨g, hg⟩ := s16e_twoConj D h.h1217 hV hc.setting hc.ne_bot
      (s1611e3_c6_v1 h6c) hs15
    obtain ⟨x, Z, h1, h2, h3, h4, h5, h6', h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
      h17, h18, h19, h20, h21⟩ :=
      s1611e3_c6_structure hc hg hperfA (fun z hz => hSC.center z hz) hAF e
    refine ⟨x, Z, h1, h2, h3, h4, h5, h6', h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
      h17, h18, h19, h20, h21, ?_⟩
    intro hAlt'
    exfalso
    have h60 : Nat.card ↥(lBar V₀ V hV L) = 60 := by
      obtain ⟨eA⟩ := hAlt'
      rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    have h168 : Nat.card ↥(lBar V₀ V hV L) = 168 := card_eq_of_isL3 hL3
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
