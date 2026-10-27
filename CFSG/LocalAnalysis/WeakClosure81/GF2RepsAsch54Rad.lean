module

public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem isCompositionFactor_of_surjective_of_isSolvable_ker {X Y : Type} [Group X] [Group Y]
    [Finite X] (f : X →* Y) (hf : Function.Surjective f) (hker : Group.IsSolvable f.ker)
    {L : Type} [Group L] (h : E1.IsCompositionFactor X L) (hnab : ∃ a b : L, a * b ≠ b * a) :
    E1.IsCompositionFactor Y L := by
  rcases isCompositionFactor_of_normal f.ker h with h1 | h2
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      hker h1 a b) hab
  · exact (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (QuotientGroup.quotientKerEquivOfSurjective f hf)).1 h2

private theorem isSolvable_ker_of_mem {G M : Type} [Group G] [Group M] {X A : Subgroup G}
    (f : ↥X →* M) (hA : Group.IsSolvable ↥A) (h : ∀ x : ↥X, f x = 1 → (x : G) ∈ A) :
    Group.IsSolvable f.ker := by
  let ι : ↥f.ker →* ↥A :=
    { toFun := fun x => ⟨((x : ↥X) : G), h x (MonoidHom.mem_ker.mp x.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := ι) fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg (fun z : ↥A => (z : G)) hab))

theorem isCompositionFactor_of_le_layer {Q : Type} [Group Q] {N : Subgroup Q}
    (hN : N ≤ CFSG.layer Q) (hn : (N.subgroupOf (CFSG.layer Q)).Normal) {L : Type} [Group L]
    (h : E1.IsCompositionFactor ↥N L) : E1.IsCompositionFactor Q L := by
  have : (CFSG.layer Q).Characteristic := CFSG.LocalCores.layer_characteristic
  have h1 : E1.IsCompositionFactor ↥(N.subgroupOf (CFSG.layer Q)) L :=
    (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (Subgroup.subgroupOfEquivOfLe hN).symm).1 h
  exact kbr_isCompositionFactor_of_normal_subgroup _
    (kbr_isCompositionFactor_of_normal_subgroup _ h1)

theorem exists_normal_le_layer_of_isComponent {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q}
    (T : Subgroup Q) (hE : CFSG.IsComponent E) :
    ∃ N : Subgroup Q, N ≤ CFSG.layer Q ∧ (N.subgroupOf (CFSG.layer Q)).Normal ∧
      N ≤ E ⊔ T ∧ (N.subgroupOf (E ⊔ T)).Normal ∧ E ≤ N := by
  set Y := E ⊔ T
  let F : ↥Y → Subgroup Q := fun g => E.map (MulAut.conj (g : Q)).toMonoidHom
  have hcomp : ∀ g : ↥Y, CFSG.IsComponent (F g) := fun g =>
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (g : Q)) hE
  have hconj : ∀ y g : Q, (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      E.map (MulAut.conj (y * g)).toMonoidHom := by
    intro y g
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hYn : Y ≤ normalizer ((⨆ g, F g : Subgroup Q) : Set Q) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy k hk
    have hle : (⨆ g, F g) ≤ (⨆ g, F g).comap (MulAut.conj y).toMonoidHom := by
      refine iSup_le fun g => ?_
      rw [← Subgroup.map_le_iff_le_comap, hconj]
      exact le_iSup F ⟨y * g, Y.mul_mem hy g.2⟩
    simpa using hle hk
  refine ⟨⨆ g, F g, iSup_le fun g => CFSG.LocalCores.component_le_layer (hcomp g), ?_, ?_,
    Subgroup.normal_subgroupOf_of_le_normalizer hYn, ?_⟩
  · refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    exact (le_iInf fun g => CFSG.LocalCores.layer_le_normalizer (hcomp g)).trans
      (Subgroup.iInf_normalizer_le_normalizer_iSup F)
  · refine iSup_le fun g => ?_
    rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Y.mul_mem (Y.mul_mem g.2 (le_sup_left (b := T) he)) (Y.inv_mem g.2)
  · intro e he
    refine le_iSup F 1 ⟨e, he, ?_⟩
    simp

theorem isSolvable_quotient_of_le_sup {Q : Type} [Group Q] {N T Y : Subgroup Q} (hNY : N ≤ Y)
    (hNYn : (N.subgroupOf Y).Normal) (hTY : T ≤ Y) (hY : Y ≤ T ⊔ N) [Group.IsSolvable ↥T] :
    Group.IsSolvable (↥Y ⧸ N.subgroupOf Y) := by
  have hYn : Y ≤ normalizer (N : Set Q) := Subgroup.le_normalizer_of_normal_subgroupOf hNY
  let f : ↥T →* ↥Y ⧸ N.subgroupOf Y := (QuotientGroup.mk' _).comp (Subgroup.inclusion hTY)
  refine Group.isSolvable_of_surjective (f := f) fun q => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Y) q
  have hy : (y : Q) ∈ ((T ⊔ N : Subgroup Q) : Set Q) := hY y.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T N (hTY.trans hYn)] at hy
  obtain ⟨t, ht, n, hn, htn⟩ := Set.mem_mul.mp hy
  refine ⟨⟨t, ht⟩, ?_⟩
  change ((Subgroup.inclusion hTY ⟨t, ht⟩ : ↥Y) : ↥Y ⧸ N.subgroupOf Y) =
    (y : ↥Y ⧸ N.subgroupOf Y)
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  change t⁻¹ * (y : Q) ∈ N
  rw [← htn, inv_mul_cancel_left]
  exact hn

theorem isSylowIn_map_top {K Q : Type} [Group K] [Group Q] [Finite K] {π : K →* Q}
    (hπ : Function.Surjective π) {S : Subgroup K} (hS : IsSylowIn 2 S ⊤) :
    IsSylowIn 2 (S.map π) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective π hπ
  have hidx : ¬ 2 ∣ S.index := by
    have h := hS.not_dvd_relIndex
    rwa [Subgroup.relIndex_top_right] at h
  let S1 : Sylow 2 Q := (hS.isPGroup.toSylow hidx).mapSurjective hπ
  have hS1 : (S1 : Subgroup Q) = S.map π := rfl
  refine ⟨le_top, hS.isPGroup.map π, ?_⟩
  rw [Subgroup.relIndex_top_right, ← hS1]
  exact S1.not_dvd_index

variable {Q : Type} [Group Q] [Finite Q]

theorem isSylowIn_inf_layer {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) :
    IsSylowIn 2 (T ⊓ CFSG.layer Q) (CFSG.layer Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.layer Q).Characteristic := CFSG.LocalCores.layer_characteristic
  exact hT.inf_normal le_top inferInstance

theorem isSolvable_normalizer_inf_layer {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) :
    Group.IsSolvable
      ↥(normalizer ((T ⊓ CFSG.layer Q : Subgroup Q) : Set Q) ⊓ CFSG.layer Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := T ⊓ CFSG.layer Q
  set W := normalizer (P : Set Q) ⊓ CFSG.layer Q
  have hPsyl : IsSylowIn 2 P (CFSG.layer Q) := isSylowIn_inf_layer hT
  have hPW : P ≤ W := le_inf le_normalizer hPsyl.le
  have hWE : W ≤ CFSG.layer Q := inf_le_right
  have : (P.subgroupOf W).Normal := Subgroup.normal_subgroupOf_of_le_normalizer inf_le_left
  have : Group.IsSolvable ↥(P.subgroupOf W) := by
    have hp : IsPGroup 2 ↥(P.subgroupOf W) :=
      hPsyl.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hPW).symm
    have := hp.isNilpotent
    infer_instance
  have : Group.IsSolvable (↥W ⧸ P.subgroupOf W) := by
    refine CFSG.FeitThompson.isSolvable_of_odd_natCard _ ?_
    rw [← Subgroup.index_eq_card, Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro hdvd
    apply hPsyl.not_dvd_relIndex
    rw [← Subgroup.relIndex_mul_relIndex P W (CFSG.layer Q) hPW hWE]
    exact hdvd.mul_right _
  exact Group.isSolvable_of_subgroup_quotient (P.subgroupOf W)

theorem isCompositionFactor_of_normalizer_inf_layer {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤)
    {L : Type} [Group L]
    (h : E1.IsCompositionFactor ↥(normalizer ((T ⊓ CFSG.layer Q : Subgroup Q) : Set Q)) L)
    (hnab : ∃ a b : L, a * b ≠ b * a) : E1.IsCompositionFactor Q L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.layer Q).Characteristic := CFSG.LocalCores.layer_characteristic
  set Z := normalizer ((T ⊓ CFSG.layer Q : Subgroup Q) : Set Q)
  let f : ↥Z →* Q ⧸ CFSG.layer Q := (QuotientGroup.mk' (CFSG.layer Q)).comp Z.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.layer Q) q
    obtain ⟨k, hk, n, hn, rfl⟩ :=
      frattini_argument le_top inferInstance (isSylowIn_inf_layer hT) (Subgroup.mem_top q)
    refine ⟨⟨n, (Subgroup.mem_inf.mp hn).2⟩, ?_⟩
    change ((n : Q) : Q ⧸ CFSG.layer Q) = ((k * n : Q) : Q ⧸ CFSG.layer Q)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).mpr hk, one_mul]
  have hkerf : Group.IsSolvable f.ker :=
    isSolvable_ker_of_mem (A := Z ⊓ CFSG.layer Q) f (isSolvable_normalizer_inf_layer hT)
      fun x hx => Subgroup.mem_inf.mpr ⟨x.2, (QuotientGroup.eq_one_iff _).mp hx⟩
  exact CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective _
    (QuotientGroup.mk'_surjective _)
    (isCompositionFactor_of_surjective_of_isSolvable_ker f hf hkerf h hnab)

theorem layer_ne_bot_of_solvableRadical_eq_bot (hrad : CFSG.solvableRadical Q = ⊥)
    (hns : ¬ Group.IsSolvable Q) : CFSG.layer Q ≠ ⊥ := by
  intro h
  apply hns
  refine Group.isSolvable_of_top_eq_bot _ (eq_bot_iff.mpr ?_)
  rw [← CFSG.SignalizerFunctorTheorem.Nonsolvable.centralizer_layer_eq_bot hrad, h]
  intro g _
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
  rw [hy, one_mul, mul_one]

theorem isSimpleGroup_of_isComponent (hrad : CFSG.solvableRadical Q = ⊥) {E : Subgroup Q}
    (hE : CFSG.IsComponent E) : IsSimpleGroup ↥E ∧ ∃ a b : ↥E, a * b ≠ b * a := by
  have hZ : Subgroup.center ↥E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : Q) ∈ Subgroup.centralizer (CFSG.layer Q : Set Q) :=
      CFSG.LocalCores.center_component_le_centralizer_layer hE ⟨x, hx, rfl⟩
    rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.centralizer_layer_eq_bot hrad] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  let e : ↥E ≃* ↥E ⧸ Subgroup.center ↥E :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := hE.1.2.1
  obtain ⟨a, b, hab⟩ := hE.1.2.2
  refine ⟨e.isSimpleGroup, e.symm a, e.symm b, fun h => hab ?_⟩
  simpa using congrArg e h

theorem comap_le_lGen {K Q : Type} [Group K] [Group Q] [Finite K]
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    {S : Subgroup K} (hno : ¬ HasCompFactor (⊤ : Subgroup K) P)
    (π : K →* Q) (hπ : Function.Surjective π) (hker : Group.IsSolvable ↥π.ker)
    {Y : Subgroup Q} (hSY : S.map π ≤ Y) (hYt : Y ≠ ⊤)
    (hY : ∀ (L : Type) [Group L], E1.IsCompositionFactor ↥Y L →
      (∃ a b : L, a * b ≠ b * a) → E1.IsCompositionFactor Q L) :
    Y.comap π ≤ lGen P ⊤ S := by
  refine le_iSup₂_of_le (Y.comap π) ⟨Subgroup.map_le_iff_le_comap.mp hSY, ?_, ?_⟩ le_rfl
  · refine lt_top_iff_ne_top.mpr fun h => hYt ?_
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ Y, h, Subgroup.map_top_of_surjective π hπ]
  · rintro ⟨L, hL, hcf, hPL⟩
    have : Finite L := isCompositionFactor_finite hcf
    have hnab := hP L hPL
    let φ : ↥(Y.comap π) →* ↥Y := π.subgroupComap Y
    have hφ : Function.Surjective φ := MonoidHom.subgroupComap_surjective π Y hπ
    have hφker : Group.IsSolvable φ.ker :=
      isSolvable_ker_of_mem φ hker fun x hx => MonoidHom.mem_ker.mpr (congrArg Subtype.val hx)
    have h1 := hY L (isCompositionFactor_of_surjective_of_isSolvable_ker φ hφ hφker hcf hnab) hnab
    have h2 : E1.IsCompositionFactor K L :=
      CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective π hπ h1
    exact hno ⟨L, hL, (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      Subgroup.topEquiv.symm).1 h2, hPL⟩

theorem exists_isComponent_comap_sup_eq_top {K Q : Type} [Group K] [Group Q] [Finite K]
    {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    {S : Subgroup K} (hS : IsSylowIn 2 S ⊤) (hno : ¬ HasCompFactor (⊤ : Subgroup K) P)
    (hne : lGen P ⊤ S ≠ ⊤) (π : K →* Q) (hπ : Function.Surjective π)
    (hker : Group.IsSolvable ↥π.ker) (hrad : CFSG.solvableRadical Q = ⊥)
    (hns : ¬ Group.IsSolvable Q) :
    ∃ E : Subgroup Q, CFSG.IsComponent E ∧ E.comap π ⊔ S = ⊤ := by
  classical
  have : Finite Q := Finite.of_surjective π hπ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.layer Q).Characteristic := CFSG.LocalCores.layer_characteristic
  have hSb : IsSylowIn 2 (S.map π) ⊤ := isSylowIn_map_top hπ hS
  have : Group.IsSolvable ↥(S.map π) := by
    have := hSb.isPGroup.isNilpotent
    infer_instance
  have hZt : normalizer ((S.map π ⊓ CFSG.layer Q : Subgroup Q) : Set Q) ≠ ⊤ := by
    intro hZ
    have hW := isSolvable_normalizer_inf_layer hSb
    rw [hZ, top_inf_eq] at hW
    refine layer_ne_bot_of_solvableRadical_eq_bot hrad hns (le_bot_iff.mp ?_)
    rw [← hrad]
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical inferInstance hW
  have hSZ : S.map π ≤ normalizer ((S.map π ⊓ CFSG.layer Q : Subgroup Q) : Set Q) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨(S.map π).mul_mem ((S.map π).mul_mem hs hx1)
      ((S.map π).inv_mem hs), (inferInstance : (CFSG.layer Q).Normal).conj_mem x hx2 s⟩
  have hZle : (normalizer ((S.map π ⊓ CFSG.layer Q : Subgroup Q) : Set Q)).comap π ≤
      lGen P ⊤ S :=
    comap_le_lGen hP hno π hπ hker hSZ hZt fun L _ h hnab =>
      isCompositionFactor_of_normalizer_inf_layer hSb h hnab
  have hZmap : normalizer ((S.map π ⊓ CFSG.layer Q : Subgroup Q) : Set Q) ≤
      (lGen P ⊤ S).map π :=
    (Subgroup.map_comap_eq_self_of_surjective hπ _).symm.le.trans (Subgroup.map_mono hZle)
  by_contra hcon'
  have hcon : ∀ E : Subgroup Q, CFSG.IsComponent E → E.comap π ⊔ S ≠ ⊤ := fun E hE h =>
    hcon' ⟨E, hE, h⟩
  have hcomp : ∀ C : Subgroup Q, CFSG.IsComponent C → C ≤ (lGen P ⊤ S).map π := by
    intro C hC
    have hCt : C ⊔ S.map π ≠ ⊤ := by
      intro htop
      refine hcon C hC ?_
      have h1 : (C.comap π ⊔ S).map π = ⊤ := by
        rw [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hπ, htop]
      have h2 := Subgroup.comap_map_eq π (C.comap π ⊔ S)
      rw [h1, Subgroup.comap_top,
        sup_of_le_left (le_sup_of_le_left (MonoidHom.ker_le_comap π C))] at h2
      exact h2.symm
    obtain ⟨N, hNl, hNln, hNY, hNYn, hCN⟩ := exists_normal_le_layer_of_isComponent (S.map π) hC
    have hgood : ∀ (L : Type) [Group L], E1.IsCompositionFactor ↥(C ⊔ S.map π) L →
        (∃ a b : L, a * b ≠ b * a) → E1.IsCompositionFactor Q L := by
      intro L _ h hnab
      rcases isCompositionFactor_of_normal (N.subgroupOf (C ⊔ S.map π)) h with h1 | h2
      · exact isCompositionFactor_of_le_layer hNl hNln
          ((CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
            (Subgroup.subgroupOfEquivOfLe hNY)).1 h1)
      · have hsol := isSolvable_quotient_of_le_sup hNY hNYn le_sup_right
          (sup_le (hCN.trans le_sup_right) le_sup_left)
        obtain ⟨a, b, hab⟩ := hnab
        exact absurd (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
          hsol h2 a b) hab
    have h := comap_le_lGen hP hno π hπ hker le_sup_right hCt hgood
    calc C ≤ C ⊔ S.map π := le_sup_left
      _ = ((C ⊔ S.map π).comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπ _).symm
      _ ≤ (lGen P ⊤ S).map π := Subgroup.map_mono h
  have hEle : CFSG.layer Q ≤ (lGen P ⊤ S).map π :=
    (CFSG.layer.eq_sSup Q).le.trans (sSup_le fun C hC => hcomp C hC)
  have hmaptop : (lGen P ⊤ S).map π = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨k, hk, n, hn, rfl⟩ :=
      frattini_argument le_top inferInstance (isSylowIn_inf_layer hSb) (Subgroup.mem_top q)
    exact Subgroup.mul_mem _ (hEle hk) (hZmap (Subgroup.mem_inf.mp hn).2)
  apply hne
  have h2 := Subgroup.comap_map_eq π (lGen P ⊤ S)
  rw [hmaptop, Subgroup.comap_top,
    sup_of_le_left ((MonoidHom.ker_le_comap π _).trans hZle)] at h2
  exact h2.symm

end CFSG.LocalAnalysis.WeakClosure81

end
