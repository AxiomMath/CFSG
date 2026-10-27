module

public import CFSG.Timmesfeld.Bridge.OddTranspThird
public import CFSG.Timmesfeld.Bridge.OddTranspSimple
public import CFSG.Timmesfeld.Bridge.OddTranspNPC
public import CFSG.Timmesfeld.Bridge.Asc72ThirdKind

public section

namespace CFSG.Timmesfeld.Bridge.OddTransp

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

variable {G : Type} [Group G] {D : Set G}

@[expose] def classIn (X : Subgroup G) (x : X) : Set X := {k | IsConj x k}

theorem setup_classIn (hS : Setup G D) {x : G} (hx : x ∈ D) {T : Set G} (hTD : T ⊆ D)
    (hT : ∀ t ∈ T, ¬ Commute t x) :
    Setup (Subgroup.closure (insert x T))
      (classIn (Subgroup.closure (insert x T)) ⟨x, Subgroup.subset_closure (Set.mem_insert x T)⟩) ∧
      ∀ t (ht : t ∈ T), (⟨t, Subgroup.subset_closure (Set.mem_insert_of_mem x ht)⟩ :
        Subgroup.closure (insert x T)) ∈
          classIn (Subgroup.closure (insert x T))
            ⟨x, Subgroup.subset_closure (Set.mem_insert x T)⟩ := by
  set X := Subgroup.closure (insert x T) with hXdef
  have hxX : x ∈ X := Subgroup.subset_closure (Set.mem_insert x T)
  have hTX : ∀ t ∈ T, t ∈ X := fun t ht => Subgroup.subset_closure (Set.mem_insert_of_mem x ht)
  have hmem : ∀ t (ht : t ∈ T), (⟨t, hTX t ht⟩ : X) ∈ classIn X ⟨x, hxX⟩ := by
    intro t ht
    obtain ⟨g, hg, hge⟩ := hS.oddT.exists_conj (hTD ht) hx (hT t ht)
    have hgX : g ∈ X := Subgroup.closure_mono (by
      rintro w (rfl | rfl)
      · exact Set.mem_insert_of_mem x ht
      · exact Set.mem_insert w T) hg
    refine (isConj_iff.mpr ⟨⟨g, hgX⟩, Subtype.ext ?_⟩).symm
    simpa using hge
  refine ⟨⟨⟨⟨x, hxX⟩, rfl⟩, ?_, ?_⟩, hmem⟩
  · refine (hS.oddT.preimage X).mono ?_
    intro k hk
    obtain ⟨c, rfl⟩ := isConj_iff.mp hk
    exact hS.conj_mem (c : G) hx
  · rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := insert x T)]
    refine Subgroup.closure_mono ?_
    rintro ⟨w, hw⟩ (hw' | hw')
    · have : (⟨w, hw⟩ : X) = ⟨x, hxX⟩ := Subtype.ext hw'
      rw [this]
      exact IsConj.refl _
    · exact hmem w hw'

theorem isBenderGroup_quotient_of_le {K : Type} [Group K] [Finite K] {E : Set K}
    (hS : Setup K E) (hE : MeetsSq E) (hdisc : Disconnected E)
    (IH : ∀ (H : Type) [Group H] [Finite H] (F : Set H), Nat.card H ≤ Nat.card K → Setup H F →
      (∀ N : Subgroup H, N.Normal → Group.IsSolvable N → N = ⊥) → MeetsSq F → Disconnected F →
      CFSG.BenderSuzuki.IsBenderGroup H) :
    CFSG.BenderSuzuki.IsBenderGroup (K ⧸ CFSG.solvableRadical K) := by
  set R := CFSG.solvableRadical K
  have hRs : Group.IsSolvable R := isSolvable_solvableRadical
  have hns := not_isSolvable hS hE
  set π := QuotientGroup.mk' R
  have hπ1 : ∀ d ∈ E, π d ≠ 1 := fun d hd h1 =>
    not_mem_of_isSolvable hS hE hRs hd ((QuotientGroup.eq_one_iff d).mp h1)
  have hS' := hS.map π (QuotientGroup.mk'_surjective R) hπ1
  refine IH _ _ (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective R)) hS'
    (fun N hN hNs => eq_bot_of_quotient_solvableRadical N hN hNs) (hE.map hS.oddT π hπ1) ?_
  obtain ⟨u, hu, w, hw, huw⟩ := hdisc
  refine ⟨π u, ⟨u, hu, rfl⟩, π w, ⟨w, hw, rfl⟩, fun h => huw ?_⟩
  have hlift : ∀ a ∈ E, ∀ b ∈ E, a⁻¹ * b ∈ R → Reach E a b := fun a ha b hb hab =>
    reach_of_inv_mul_mem_solvable hS hns hRs ha hb hab
  exact reach_of_reach_quotient hS.oddT hlift hu hw h

theorem mem_conj_sylow_iff {K : Type*} [Group K] {p : ℕ} {P : Sylow p K} {g y : K} :
    y ∈ ((g • P : Sylow p K) : Subgroup K) ↔ g⁻¹ * y * g ∈ (P : Subgroup K) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem ncard_inter_sylow_eq [Finite G] (hN : IsNormalSet D) (S₁ S₂ : Sylow 2 G) :
    (D ∩ (S₂ : Set G)).ncard = (D ∩ (S₁ : Set G)).ncard := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S₁ S₂
  have himage : (fun y => g * y * g⁻¹) '' (D ∩ (S₁ : Set G)) =
      D ∩ ((g • S₁ : Sylow 2 G) : Set G) := by
    ext y
    constructor
    · rintro ⟨w, ⟨hwD, hwS⟩, rfl⟩
      refine ⟨hN g w hwD, ?_⟩
      show g * w * g⁻¹ ∈ ((g • S₁ : Sylow 2 G) : Subgroup G)
      rw [mem_conj_sylow_iff, show g⁻¹ * (g * w * g⁻¹) * g = w by group]
      exact hwS
    · rintro ⟨hyD, hyS⟩
      refine ⟨g⁻¹ * y * g, ⟨by simpa using hN g⁻¹ y hyD, ?_⟩, by group⟩
      exact mem_conj_sylow_iff.mp hyS
  rw [← himage, Set.ncard_image_of_injective _ (fun u v huv => by simpa using huv)]

theorem exists_conj_mem_of_isPGroup [Finite G] (hN : IsNormalSet D) (S₀ : Sylow 2 G) {a e : G}
    (hL : ∀ s ∈ D ∩ (S₀ : Set G), Commute s a ∧ Commute s e) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPC : ∀ p ∈ P, Commute p a ∧ Commute p e) :
    ∃ g : G, Commute g a ∧ Commute g e ∧ ∀ y ∈ P, y ∈ D → g * y * g⁻¹ ∈ D ∩ (S₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({a, e} : Set G) with hCdef
  have hmemC : ∀ y : G, Commute y a → Commute y e → y ∈ C := by
    intro y hya hye
    rw [Subgroup.mem_centralizer_iff]
    rintro w (rfl | rfl)
    · exact hya.eq.symm
    · exact hye.eq.symm
  have hCcomm : ∀ c ∈ C, Commute c a ∧ Commute c e := fun c hc =>
    ⟨(Subgroup.mem_centralizer_iff.mp hc a (by simp)).symm,
      (Subgroup.mem_centralizer_iff.mp hc e (by simp)).symm⟩
  have hP1 : IsPGroup 2 ((S₀ : Subgroup G).subgroupOf C) := S₀.isPGroup'.comap_subtype
  have hP2 : IsPGroup 2 (P.subgroupOf C) := hP.comap_subtype
  obtain ⟨R₁, hR₁⟩ := hP1.exists_le_sylow
  obtain ⟨R₂, hR₂⟩ := hP2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C R₁ R₂
  have hR₁G : IsPGroup 2 ((R₁ : Subgroup C).map C.subtype) := R₁.isPGroup'.map _
  obtain ⟨S₂, hS₂⟩ := hR₁G.exists_le_sylow
  have hsub : D ∩ (S₀ : Set G) ⊆ D ∩ (S₂ : Set G) := by
    rintro s ⟨hsD, hsS⟩
    have hsC : s ∈ C := hmemC s (hL s ⟨hsD, hsS⟩).1 (hL s ⟨hsD, hsS⟩).2
    exact ⟨hsD, hS₂ ⟨⟨s, hsC⟩, hR₁ hsS, rfl⟩⟩
  have heq : D ∩ (S₂ : Set G) = D ∩ (S₀ : Set G) :=
    (Set.eq_of_subset_of_ncard_le hsub (ncard_inter_sylow_eq hN S₀ S₂).le
      (Set.toFinite _)).symm
  refine ⟨((c : C) : G)⁻¹, (hCcomm _ c.2).1.inv_left, (hCcomm _ c.2).2.inv_left, ?_⟩
  intro y hy hyD
  have hyC : y ∈ C := hmemC y (hPC y hy).1 (hPC y hy).2
  have hyR₂ : (⟨y, hyC⟩ : C) ∈ (R₂ : Subgroup C) := hR₂ hy
  rw [← hc, mem_conj_sylow_iff] at hyR₂
  have hmem : ((c : C) : G)⁻¹ * y * ((c : C) : G) ∈ D ∩ (S₂ : Set G) :=
    ⟨by simpa using hN ((c : C) : G)⁻¹ y hyD, hS₂ ⟨_, hyR₂, rfl⟩⟩
  rw [heq] at hmem
  simpa using hmem

theorem false_of_eq_mul [Finite G] (hS : Setup G D) {a e y : G} (htri : IsTriangle D a y e)
    {m : ℕ} (hm : Odd m) (hord : orderOf (a * e * y) = 2 * m) (hay : ¬ Reach D a y) {x : G}
    (hx : x ∈ D) (hax : ¬ Reach D a x) {u w : G} (hu : u ∈ D)
    (hut : Commute u ((a * e * y) ^ m)) (heq : (a * e * y) ^ m = u * w) (hwa : Commute w a)
    (hwx : Commute w x) : False := by
  set t := (a * e * y) ^ m with htdef
  obtain ⟨htt, -, hta, hte, -, haet⟩ := htri.third_kind hS.oddT hS.normal hm hord
  have hSt := localSetup hS htri hm hord hay
  have huC : u ∈ centSet D t := ⟨hu, hut⟩
  have heC : e ∈ centSet D t := ⟨htri.2.1, hte.symm⟩
  obtain ⟨h, hh⟩ := isConj_iff.mp (hSt.isConj (show (⟨e, mem_localGroup_of_mem heC⟩ :
    localGroup D t) ∈ localSet D t from heC) (show (⟨u, mem_localGroup_of_mem huC⟩ :
    localGroup D t) ∈ localSet D t from huC))
  have hh' : (h : G) * e * (h : G)⁻¹ = u := by simpa using congrArg Subtype.val hh
  have hht : Commute (h : G) t := commute_of_mem_localGroup h.2
  have ha2 := hS.oddT.mul_self_eq_one htri.1
  have he2 := hS.oddT.mul_self_eq_one htri.2.1
  have hcae : Commute a e := htri.2.2.2.2.1
  have hw : w = (h : G) * a * (h : G)⁻¹ * ((h : G) * (a * e * t) * (h : G)⁻¹) := by
    have h1 : w = u⁻¹ * t := by rw [heq]; group
    rw [h1, ← hh', hS.oddT.inv_eq (hS.conj_mem _ htri.2.1)]
    have h2 : e * t = a * (a * e * t) := by rw [← mul_assoc, ← mul_assoc, ha2, one_mul]
    calc (h : G) * e * (h : G)⁻¹ * t = (h : G) * (e * t) * (h : G)⁻¹ := by
          rw [mul_assoc ((h : G) * e), hht.inv_left.eq]; group
      _ = (h : G) * (a * (a * e * t)) * (h : G)⁻¹ := by rw [h2]
      _ = (h : G) * a * (h : G)⁻¹ * ((h : G) * (a * e * t) * (h : G)⁻¹) := by group
  have hrD : (h : G) * a * (h : G)⁻¹ ∈ D := hS.conj_mem _ htri.1
  have hsD : (h : G) * (a * e * t) * (h : G)⁻¹ ∈ D := hS.conj_mem _ haet
  have hrs : (h : G) * a * (h : G)⁻¹ ≠ (h : G) * (a * e * t) * (h : G)⁻¹ := by
    intro hrs
    have h1 : a = a * e * t := by simpa using hrs
    have h2 : e * t = 1 := by
      calc e * t = a * (a * e * t) := by rw [← mul_assoc, ← mul_assoc, ha2, one_mul]
        _ = 1 := by rw [← h1, ha2]
    have h3 : t = e := by
      have := eq_inv_of_mul_eq_one_right h2
      rwa [hS.oddT.inv_eq htri.2.1] at this
    exact thirdKind_z_not_mem hS htri hm hord hay (htdef ▸ h3 ▸ htri.2.1)
  have hcrs : Commute ((h : G) * a * (h : G)⁻¹) ((h : G) * (a * e * t) * (h : G)⁻¹) := by
    have hc : Commute a (a * e * t) :=
      ((Commute.refl a).mul_right hcae).mul_right hta.symm
    exact (Commute.conj_iff (h : G)).mpr hc
  rw [hw] at hwa hwx
  have hxr := ((hS.oddT.commute_mul_iff hrD hsD hx hrs hcrs).mp hwx.symm).1
  have har := ((hS.oddT.commute_mul_iff hrD hsD htri.1 hrs hcrs).mp hwa.symm).1
  exact hax (reach_trans (reach_of_commute htri.1 hrD har) (reach_of_commute hrD hx hxr.symm))

theorem commute_coe_iff {H : Subgroup G} {u v : H} : Commute (u : G) (v : G) ↔ Commute u v :=
  ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem isBenderGroup_of_lt [Finite G] (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hDD : MeetsSq D)
    (hdisc : Disconnected D)
    (IH : ∀ (H : Type) [Group H] [Finite H] (F : Set H), Nat.card H < Nat.card G → Setup H F →
      (∀ N : Subgroup H, N.Normal → Group.IsSolvable N → N = ⊥) → MeetsSq F → Disconnected F →
      CFSG.BenderSuzuki.IsBenderGroup H) :
    CFSG.BenderSuzuki.IsBenderGroup G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hS.oddT
  have hN := hS.normal
  have hnorm : ∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K := by
    intro K hK
    rcases eq_bot_or_eq_top_of_normal hS hrad hDD K with h | h
    · exact Or.inl h
    · exact Or.inr (h ▸ le_top)
  have hZ : Subgroup.center G = ⊥ := hrad _ inferInstance
    (Group.isSolvable_of_comm fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x))
  by_cases hnp : Moufang.NoPolar D
  · exact isBenderGroup_of_noPolar hS hrad hdisc hnp
  obtain ⟨a, ha, b, hb, hab, hne, habD⟩ : ∃ a ∈ D, ∃ b ∈ D, Commute a b ∧ a ≠ b ∧ a * b ∉ D := by
    unfold Moufang.NoPolar at hnp
    push Not at hnp
    exact hnp
  exfalso
  obtain ⟨x, hx, hax, htri, n, hn, hn1, hord⟩ := exists_thirdKind hS hdisc hnorm ha hb hne hab habD
  set z := (a * b * x) ^ n with hzdef
  obtain ⟨hzz, hz1, hza, hzb, hzx, hdD⟩ := htri.third_kind hD hN hn hord
  set d := a * b * z with hddef
  have hdab : Commute d a ∧ Commute d b :=
    (hD.commute_mul_iff ha hb hdD hne hab).mp ((Commute.refl (a * b)).mul_left (hza.mul_right hzb))
  obtain ⟨v₀, hv₀, hav₀, hcav₀, hav₀D⟩ := exists_mul_mem hS hDD ha
  have hbv₀ : Commute b v₀ := (commute_iff_of_mul_mem hS ha hv₀ hav₀ hcav₀ hav₀D hb).mp hab.symm
  have hdv₀ : Commute d v₀ := (commute_iff_of_mul_mem hS ha hv₀ hav₀ hcav₀ hav₀D hdD).mp hdab.1
  have hpair : ({a, b, d, v₀} : Set G).Pairwise Commute := by
    have h1 := hab; have h2 := hdab.1.symm; have h3 := hcav₀; have h4 := hdab.2.symm
    have h5 := hbv₀; have h6 := hdv₀
    have h1' := hab.symm; have h2' := hdab.1; have h3' := hcav₀.symm; have h4' := hdab.2
    have h5' := hbv₀.symm; have h6' := hdv₀.symm
    intro s hs t ht _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption
  have hP₀ : IsPGroup 2 (Subgroup.closure ({a, b, d, v₀} : Set G)) := by
    refine isPGroup_closure_of_pairwise hpair ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact hD.mul_self_eq_one ha
    · exact hD.mul_self_eq_one hb
    · exact hD.mul_self_eq_one hdD
    · exact hD.mul_self_eq_one hv₀
  obtain ⟨S₀, hS₀⟩ := hP₀.exists_le_sylow
  have hmemS₀ : ∀ s ∈ ({a, b, d, v₀} : Set G), s ∈ S₀ := fun s hs =>
    hS₀ (Subgroup.subset_closure hs)
  have ha₀ : a ∈ D ∩ (S₀ : Set G) := ⟨ha, hmemS₀ a (by simp)⟩
  have hb₀ : b ∈ D ∩ (S₀ : Set G) := ⟨hb, hmemS₀ b (by simp)⟩
  have hd₀ : d ∈ D ∩ (S₀ : Set G) := ⟨hdD, hmemS₀ d (by simp)⟩
  have hv₀₀ : v₀ ∈ D ∩ (S₀ : Set G) := ⟨hv₀, hmemS₀ v₀ (by simp)⟩
  have hav₀₀ : a * v₀ ∈ D ∩ (S₀ : Set G) := ⟨hav₀D, S₀.mul_mem ha₀.2 hv₀₀.2⟩
  have hLcomm : ∀ s ∈ D ∩ (S₀ : Set G), ∀ t ∈ D ∩ (S₀ : Set G), Commute s t :=
    fun s hs t ht => hD.commute_of_isPGroup S₀.isPGroup' hs.1 ht.1 hs.2 ht.2
  have hzabd : z = a * b * d := by
    rw [hddef, ← mul_assoc, IsTriangle.uv_mul_self hD htri, one_mul]
  have hLx : ∀ s ∈ D ∩ (S₀ : Set G), ¬ Commute s x := fun s hs hsx =>
    hax (reach_trans (reach_of_commute ha hs.1 (hLcomm a ha₀ s hs))
      (reach_of_commute hs.1 hx hsx))
  obtain ⟨hSX, hmemX⟩ := setup_classIn hS hx Set.inter_subset_left hLx
  set X := Subgroup.closure (insert x (D ∩ (S₀ : Set G))) with hXdef
  have hxX : x ∈ X := Subgroup.subset_closure (Set.mem_insert x _)
  have hLX : ∀ s ∈ D ∩ (S₀ : Set G), s ∈ X := fun s hs =>
    Subgroup.subset_closure (Set.mem_insert_of_mem x hs)
  set EX := classIn X ⟨x, hxX⟩ with hEXdef
  have hEXD : ∀ k ∈ EX, (k : G) ∈ D := by
    intro k hk
    obtain ⟨c, rfl⟩ := isConj_iff.mp hk
    exact hS.conj_mem (c : G) hx
  set a' : X := ⟨a, hLX a ha₀⟩ with ha'def
  set b' : X := ⟨b, hLX b hb₀⟩ with hb'def
  set x' : X := ⟨x, hxX⟩ with hx'def
  have ha'E : a' ∈ EX := hmemX a ha₀
  have hb'E : b' ∈ EX := hmemX b hb₀
  have hx'E : x' ∈ EX := IsConj.refl _
  have hMX : MeetsSq EX := by
    refine ⟨a', ha'E, ⟨v₀, hLX v₀ hv₀₀⟩, hmemX v₀ hv₀₀, fun h => hav₀ (congrArg Subtype.val h),
      commute_coe_iff.mp hcav₀, ?_⟩
    exact hmemX (a * v₀) hav₀₀
  have hdiscX : Disconnected EX := by
    refine ⟨a', ha'E, x', hx'E, fun h => hax ?_⟩
    exact reach_of_reach_subgroup X (reach_mono (fun k hk => hEXD k hk) h)
  have hzX : z ∈ X := by
    rw [hzabd]
    exact X.mul_mem (X.mul_mem (hLX a ha₀) (hLX b hb₀)) (hLX d hd₀)
  have hzcomm : ∀ g ∈ X, Commute g z := by
    intro g hg
    have hle : X ≤ Subgroup.centralizer {z} := by
      rw [hXdef, Subgroup.closure_le]
      rintro w (rfl | hw)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzx.symm
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hzabd]
        exact (((hLcomm w hw a ha₀).mul_right (hLcomm w hw b hb₀)).mul_right
          (hLcomm w hw d hd₀)).eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hXne : X ≠ ⊤ := by
    intro htop
    apply hz1
    have hzc : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g =>
      (hzcomm g (htop ▸ Subgroup.mem_top g)).eq
    rw [hZ] at hzc
    exact (Subgroup.mem_bot).mp hzc
  have hXcard : Nat.card X < Nat.card G := by
    rw [← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hXne)
  have hBX : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ CFSG.solvableRadical X) :=
    isBenderGroup_quotient_of_le hSX hMX hdiscX fun H _ _ F hH =>
      IH H F (lt_of_le_of_lt hH hXcard)
  have hRX := solvableRadical_eq_zStar hSX hMX
  have hBX' : CFSG.BenderSuzuki.IsBenderGroup (X ⧸ zStar X) :=
    isBenderGroup_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hRX.symm) hBX
  have hperfX := commutator_eq_top hSX hMX
  have hnpc := noPerfectCentralExt_of_isBenderGroup hSX hperfX hBX'
  have hP' : IsPGroup 2 ((S₀ : Subgroup G).subgroupOf X) := S₀.isPGroup'.comap_subtype
  obtain ⟨T, hT⟩ := hP'.exists_le_sylow
  have hLT : ∀ s (hs : s ∈ D ∩ (S₀ : Set G)), (⟨s, hLX s hs⟩ : X) ∈ T := fun s hs =>
    hT (Subgroup.mem_subgroupOf.mpr hs.2)
  set z' : X := ⟨z, hzX⟩ with hz'def
  have hz'T : z' ∈ T := hT (Subgroup.mem_subgroupOf.mpr (show z ∈ (S₀ : Subgroup G) by
    rw [hzabd]; exact S₀.mul_mem (S₀.mul_mem ha₀.2 hb₀.2) hd₀.2))
  have hz'c : z' ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (hzcomm g g.2).eq
  set Q := CFSG.pCore 2 X with hQdef
  have hz'Q : z' ∈ Q := by
    have hle : Subgroup.zpowers z' ≤ Subgroup.center X := Subgroup.zpowers_le.mpr hz'c
    have hn' : (Subgroup.zpowers z').Normal := Subgroup.normal_of_le_center hle
    have hz'z' : z' * z' = 1 := Subtype.ext hzz
    have h2 : IsPGroup 2 (Subgroup.zpowers z') := by
      rintro ⟨g, hg⟩
      refine ⟨1, Subtype.ext ?_⟩
      rcases (mem_zpowers_of_mul_self hz'z').mp hg with rfl | rfl
      · simp
      · simp [pow_two, hz'z']
    have hle2 : Subgroup.zpowers z' ≤ Q := le_sSup ⟨hn', h2⟩
    exact hle2 (Subgroup.mem_zpowers _)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  obtain ⟨q, hqQ, hqa⟩ : ∃ q ∈ Q, ¬ Commute q a' := by
    by_contra hcon
    push Not at hcon
    have hQc : Q ≤ Subgroup.center X := by
      intro q hq
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.closure EX := hSX.gen ▸ Subgroup.mem_top g
      have hgen : ∀ k ∈ EX, Commute q k := by
        intro k hk
        obtain ⟨h, rfl⟩ := isConj_iff.mp (hSX.isConj ha'E hk)
        have h1 := hcon (h⁻¹ * q * h⁻¹⁻¹)
          ((CFSG.pCore_normal (p := 2) (G := X)).conj_mem q hq h⁻¹)
        have h2 := h1.map (MulAut.conj h).toMonoidHom
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2
        convert h2 using 1
        group
      exact (Asc72.commute_of_mem_closure (S := {q}) (T := EX)
        (fun u hu k hk => by rw [Set.mem_singleton_iff] at hu; rw [hu]; exact hgen k hk)
        (Subgroup.subset_closure rfl) hg).eq.symm
    have hcomm0 : ⁅Q, (⊤ : Subgroup X)⁆ = ⊥ :=
      Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hQc
    have hle := hnpc ⊥ inferInstance bot_le (hcomm0 ▸ le_rfl)
    rw [hperfX, inf_top_eq] at hle
    exact hz'1 ((Subgroup.mem_bot).mp (hle hz'Q))
  set e' : X := q * a' * q⁻¹ with he'def
  have he'E : e' ∈ EX := hSX.conj_mem q ha'E
  have hQT : Q ≤ T := CFSG.pCore_isPGroup.le_sylow_of_normal T
  have he'T : e' ∈ T := T.mul_mem (T.mul_mem (hQT hqQ) (hLT a ha₀)) (T.inv_mem (hQT hqQ))
  have he'a : e' * a'⁻¹ ∈ Q := by
    have h1 := (CFSG.pCore_normal (p := 2) (G := X)).conj_mem _ (Q.inv_mem hqQ) a'
    have e1 : e' * a'⁻¹ = q * (a' * q⁻¹ * a'⁻¹) := by rw [he'def]; group
    rw [e1]
    exact Q.mul_mem hqQ h1
  set e : G := (e' : G) with hedef
  have he : e ∈ D := hEXD e' he'E
  have hcae' : Commute a' e' := hSX.oddT.commute_of_isPGroup T.isPGroup' ha'E he'E
    (hLT a ha₀) he'T
  have hcae : Commute a e := commute_coe_iff.mpr hcae'
  have hae : a ≠ e := by
    intro h
    apply hqa
    have h1 : a' = e' := Subtype.ext h
    show q * a' = a' * q
    calc q * a' = q * a' * q⁻¹ * q := by group
      _ = a' * q := by rw [← he'def, ← h1]
  have haeD : a * e ∉ D := by
    intro haeD
    have haeX : a * e ∈ X := X.mul_mem (hLX a ha₀) e'.2
    have hae_x : ¬ Commute (a * e) x := fun hc =>
      hax (reach_trans (reach_of_commute ha haeD ((Commute.refl a).mul_right hcae))
        (reach_of_commute haeD hx hc))
    obtain ⟨g, hg, hge⟩ := hD.exists_conj haeD hx hae_x
    have hgX : g ∈ X := Subgroup.closure_le _ |>.mpr (by
      rintro w (rfl | rfl)
      · exact haeX
      · exact hxX) hg
    have haeE : (⟨a * e, haeX⟩ : X) ∈ EX :=
      (isConj_iff.mpr ⟨⟨g, hgX⟩, Subtype.ext (by simpa using hge)⟩).symm
    have haeQ : (⟨a * e, haeX⟩ : X) ∈ Q := by
      have h1 : (⟨a * e, haeX⟩ : X) = a'⁻¹ * (e' * a'⁻¹) * a'⁻¹⁻¹ := by
        rw [show a'⁻¹ * (e' * a'⁻¹) * a'⁻¹⁻¹ = a'⁻¹ * e' by group]
        apply Subtype.ext
        show a * e = ((a' : G))⁻¹ * (e' : G)
        rw [show (a' : G) = a from rfl, hD.inv_eq ha]
      rw [h1]
      exact (CFSG.pCore_normal (p := 2) (G := X)).conj_mem _ he'a a'⁻¹
    have hEQ : EX ⊆ Q := by
      intro k hk
      obtain ⟨h, rfl⟩ := isConj_iff.mp (hSX.isConj haeE hk)
      exact (CFSG.pCore_normal (p := 2) (G := X)).conj_mem _ haeQ h
    have hXQ : (⊤ : Subgroup X) ≤ Q := by
      rw [← hSX.gen, Subgroup.closure_le]
      exact hEQ
    apply not_isSolvable hSX hMX
    have hQs : Group.IsSolvable Q := by
      have := (CFSG.pCore_isPGroup (p := 2) (G := X)).isNilpotent
      infer_instance
    exact Group.isSolvable_of_surjective (f := Q.subtype)
      (fun g => ⟨⟨g, hXQ (Subgroup.mem_top g)⟩, rfl⟩)
  obtain ⟨y, hy, hay, htri₂, m, hm, hm1, hord₂⟩ :=
    exists_thirdKind hS hdisc hnorm ha he hae hcae haeD
  obtain ⟨htt, -, hta, hte, -, haet⟩ := htri₂.third_kind hD hN hm hord₂
  have hpair₂ : ({a, e, a * e * (a * e * y) ^ m} : Set G).Pairwise Commute := by
    have h1 := hcae; have h1' := hcae.symm
    have h2 : Commute a (a * e * (a * e * y) ^ m) :=
      ((Commute.refl a).mul_right hcae).mul_right hta.symm
    have h2' := h2.symm
    have h3 : Commute e (a * e * (a * e * y) ^ m) :=
      (hcae.symm.mul_right (Commute.refl e)).mul_right hte.symm
    have h3' := h3.symm
    intro s hs t ht _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption
  have hP₂ : IsPGroup 2 (Subgroup.closure ({a, e, a * e * (a * e * y) ^ m} : Set G)) := by
    refine isPGroup_closure_of_pairwise hpair₂ ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hD.mul_self_eq_one ha
    · exact hD.mul_self_eq_one he
    · exact hD.mul_self_eq_one haet
  have hgen₂ : ∀ u ∈ ({a, e, a * e * (a * e * y) ^ m} : Set G), Commute u a ∧ Commute u e := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu | hu <;> rw [hu]
    · exact ⟨Commute.refl a, hcae⟩
    · exact ⟨hcae.symm, Commute.refl e⟩
    · exact ⟨(((Commute.refl a).mul_right hcae).mul_right hta.symm).symm,
        ((hcae.symm.mul_right (Commute.refl e)).mul_right hte.symm).symm⟩
  have hPC : ∀ p ∈ Subgroup.closure ({a, e, a * e * (a * e * y) ^ m} : Set G),
      Commute p a ∧ Commute p e := by
    intro p hp
    constructor
    · exact Asc72.commute_of_mem_closure (S := {a, e, a * e * (a * e * y) ^ m}) (T := {a})
        (fun u hu w hw => by
          rw [Set.mem_singleton_iff] at hw; rw [hw]; exact (hgen₂ u hu).1) hp
        (Subgroup.subset_closure rfl)
    · exact Asc72.commute_of_mem_closure (S := {a, e, a * e * (a * e * y) ^ m}) (T := {e})
        (fun u hu w hw => by
          rw [Set.mem_singleton_iff] at hw; rw [hw]; exact (hgen₂ u hu).2) hp
        (Subgroup.subset_closure rfl)
  have hL : ∀ s ∈ D ∩ (S₀ : Set G), Commute s a ∧ Commute s e := by
    intro s hs
    refine ⟨hLcomm s hs a ha₀, ?_⟩
    exact commute_coe_iff.mpr (hSX.oddT.commute_of_isPGroup T.isPGroup' (hmemX s hs) he'E
      (hLT s hs) he'T)
  obtain ⟨g, hga, hge, hgP⟩ := exists_conj_mem_of_isPGroup hN S₀ hL hP₂ hPC
  set y₂ := g * y * g⁻¹ with hy₂def
  have hga' : g * a * g⁻¹ = a := by rw [hga.eq, mul_inv_cancel_right]
  have hge' : g * e * g⁻¹ = e := by rw [hge.eq, mul_inv_cancel_right]
  have hconj_aey : g * (a * e * y) * g⁻¹ = a * e * y₂ := by
    calc g * (a * e * y) * g⁻¹ = g * a * g⁻¹ * (g * e * g⁻¹) * (g * y * g⁻¹) := by group
      _ = a * e * y₂ := by rw [hga', hge']
  have hconj_back : ∀ w : G, g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w := fun w => by group
  have htri₃ : IsTriangle D a y₂ e := by
    refine ⟨ha, he, hS.conj_mem g hy, hae, hcae, fun h => ?_, fun h => ?_⟩
    · apply htri₂.2.2.2.2.2.1
      have h1 := (Commute.conj_iff g⁻¹).mpr h
      rwa [← hga', hconj_back, hconj_back] at h1
    · apply htri₂.2.2.2.2.2.2
      have h1 := (Commute.conj_iff g⁻¹).mpr h
      rwa [← hge', hconj_back, hconj_back] at h1
  have hord₃ : orderOf (a * e * y₂) = 2 * m := by
    rw [← hconj_aey, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hord₂]
  have hay₂ : ¬ Reach D a y₂ := by
    intro h
    apply hay
    have h1 := reach_conj hN g⁻¹ h
    rwa [← hga', hconj_back, hconj_back] at h1
  have ht₂ : (a * e * y₂) ^ m = g * (a * e * y) ^ m * g⁻¹ := by rw [← hconj_aey, conj_pow]
  have haet₂ : a * e * (a * e * y₂) ^ m ∈ D ∩ (S₀ : Set G) := by
    have h1 := hgP _ (Subgroup.subset_closure (by simp)) haet
    have e1 : g * (a * e * (a * e * y) ^ m) * g⁻¹ = a * e * (a * e * y₂) ^ m := by
      rw [ht₂]
      calc g * (a * e * (a * e * y) ^ m) * g⁻¹ =
          g * a * g⁻¹ * (g * e * g⁻¹) * (g * (a * e * y) ^ m * g⁻¹) := by group
        _ = a * e * (g * (a * e * y) ^ m * g⁻¹) := by rw [hga', hge']
    rwa [e1] at h1
  set t₂ := (a * e * y₂) ^ m with ht₂def
  obtain ⟨-, -, -, hte₂, -, -⟩ := htri₃.third_kind hD hN hm hord₃
  have haet₂X : a * e * t₂ ∈ X := hLX _ haet₂
  have hKH : ThirdKindHyp X EX T a' x' b' n := by
    refine ⟨hSX, ⟨ha'E, hb'E, hx'E, fun h => hne (congrArg Subtype.val h),
      commute_coe_iff.mp hab, fun h => htri.2.2.2.2.2.1 (commute_coe_iff.mpr h),
      fun h => htri.2.2.2.2.2.2 (commute_coe_iff.mpr h)⟩, hn, hn1, ?_, hLT a ha₀, hLT b hb₀,
      ?_, ?_, hnpc⟩
    · rw [← Subgroup.orderOf_coe]
      exact hord
    · have h1 : (a' * b' * x') ^ n = z' := Subtype.ext (by rw [SubgroupClass.coe_pow]; rfl)
      rw [h1]
      exact hz'T
    · rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := insert x (D ∩ (S₀ : Set G)))]
      refine Subgroup.closure_mono ?_
      rintro ⟨w, hw⟩ (hw' | hw')
      · left
        exact Subtype.ext hw'
      · right
        exact ⟨hmemX w hw', hLT w hw'⟩
  obtain ⟨-, hmain⟩ := hKH.main
  obtain ⟨⟨u', w'⟩, ⟨hu', hw', heq'⟩, -⟩ := hmain a' ⟨ha'E, hLT a ha₀⟩ ⟨a * e * t₂, haet₂X⟩
    ⟨hmemX _ haet₂, hLT _ haet₂⟩ e' he'E he'a
  have hwc := Subgroup.mem_center_iff.mp hw'.2
  set T₂ : X := a' * ⟨a * e * t₂, haet₂X⟩ * e' with hT₂def
  have hT₂ : (T₂ : G) = t₂ := by
    show a * (a * e * t₂) * e = t₂
    rw [show a * (a * e * t₂) * e = a * a * e * (t₂ * e) by group, hte₂.eq,
      hD.mul_self_eq_one ha, one_mul, ← mul_assoc, hD.mul_self_eq_one he, one_mul]
  have heq : t₂ = (u' : G) * (w' : G) := by
    rw [← hT₂, heq']
    rfl
  have hut : Commute (u' : G) t₂ := by
    have hu'eq : u' = T₂ * w'⁻¹ := eq_mul_inv_of_mul_eq heq'.symm
    have h1 : Commute u' T₂ := by
      rw [hu'eq]
      exact (Commute.refl _).mul_left
        (Subgroup.mem_center_iff.mp ((Subgroup.center X).inv_mem hw'.2) _).symm
    rw [← hT₂]
    exact commute_coe_iff.mpr h1
  have hwa : Commute (w' : G) a := commute_coe_iff.mpr (hwc a').symm
  have hwx : Commute (w' : G) x := commute_coe_iff.mpr (hwc x').symm
  exact false_of_eq_mul hS htri₃ hm hord₃ hay₂ hx hax (hEXD u' hu') hut heq hwa hwx

theorem oddTranspBender : OddTranspBender := by
  suffices key : ∀ k : ℕ, ∀ (G : Type) [Group G] [Finite G] (D : Set G), Nat.card G = k →
      Setup G D → (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → MeetsSq D →
      Disconnected D → CFSG.BenderSuzuki.IsBenderGroup G by
    intro G _ _ D hS hrad hDD hdisc
    exact key _ G D rfl hS hrad hDD hdisc
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro G _ _ D hk hS hrad hDD hdisc
    exact isBenderGroup_of_lt hS hrad hDD hdisc fun H _ _ F hH => ih _ (hk ▸ hH) H F rfl

theorem oddTranspRadical :
    ∀ (G : Type) [Group G] [Finite G] (D : Set G), Asc72.IsOddTransp D →
      Connectivity.IsNormalSet D → Subgroup.closure D = ⊤ →
      (∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) → Connectivity.Disconnected D →
      CFSG.solvableRadical G = zStar G ∧
        CFSG.BenderSuzuki.IsBenderGroup (G ⧸ CFSG.solvableRadical G) := by
  intro G _ _ D hD hN hgen hDD hdisc
  have hS := setup_of_disconnected hD hN hgen hdisc
  exact ⟨solvableRadical_eq_zStar hS hDD, isBenderGroup_quotient_of_le hS hDD hdisc
    fun H _ _ F _ hS' hrad' hF hdisc' => oddTranspBender H F hS' hrad' hF hdisc'⟩

theorem oddTranspZStar : OddTranspZStar := by
  intro G _ _ D hD hN hgen hDD hdisc
  obtain ⟨hR, hB⟩ := oddTranspRadical G D hD hN hgen hDD hdisc
  exact isBenderGroup_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hR.symm) hB

end CFSG.Timmesfeld.Bridge.OddTransp
