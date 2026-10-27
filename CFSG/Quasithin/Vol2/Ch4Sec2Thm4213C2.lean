module

public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212C
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Nat
public import CFSG.Quasithin.Background.B5FinS8Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative Matrix Pointwise

variable {G : Type} [Group G] [Finite G]

namespace T4213N

@[expose] noncomputable def heartAdd : ↥(evenWeight 8) →+ ⋀[ZMod 2]^2 (Fin 4 → ZMod 2) :=
  B5FinS8.qAdd.comp (evenWeight 8).subtype

theorem heartAdd_apply (x : ↥(evenWeight 8)) :
    heartAdd x = (B5FinWedge.wedgeEquiv4 (ZMod 2)).symm (B5FinS8.qform (x : Fin 8 → ZMod 2)) :=
  rfl

theorem mem_evenWeight {m : ℕ} {x : Fin m → ZMod 2} : x ∈ evenWeight m ↔ ∑ i, x i = 0 :=
  AddMonoidHom.mem_ker

theorem heartAdd_surjective : Function.Surjective heartAdd := by
  intro t
  obtain ⟨x, hx, hxq⟩ := B5FinS8.exists_qform_eq ((B5FinWedge.wedgeEquiv4 (ZMod 2)) t)
  refine ⟨⟨x, mem_evenWeight.mpr hx⟩, ?_⟩
  rw [heartAdd_apply]
  change (B5FinWedge.wedgeEquiv4 (ZMod 2)).symm (B5FinS8.qform x) = t
  rw [hxq, LinearEquiv.symm_apply_apply]

theorem const_iff (x : Fin 8 → ZMod 2) :
    (∀ i j, x i = x j) ↔ (x = 0 ∨ x = fun _ => 1) := by
  revert x
  decide +kernel

theorem heartAdd_ker : heartAdd.ker = constWeight 8 := by
  ext x
  rw [AddMonoidHom.mem_ker, heartAdd_apply, LinearEquiv.map_eq_zero_iff]
  rw [B5FinS8.qform_eq_zero_iff _ (mem_evenWeight.mp x.2)]
  change _ ↔ ∀ i j, (x : Fin 8 → ZMod 2) i = (x : Fin 8 → ZMod 2) j
  rw [const_iff]

@[expose] noncomputable def heartEquiv : AltHeart 8 ≃+ ⋀[ZMod 2]^2 (Fin 4 → ZMod 2) :=
  (QuotientAddGroup.quotientAddEquivOfEq heartAdd_ker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective heartAdd heartAdd_surjective)

theorem heartEquiv_mk (x : ↥(evenWeight 8)) :
    heartEquiv (QuotientAddGroup.mk x) = heartAdd x := rfl

theorem heartEquiv_perm (σ : alternatingGroup (Fin 8)) (x : ↥(evenWeight 8)) :
    heartEquiv (QuotientAddGroup.mk (permWeight 8 (σ : Equiv.Perm (Fin 8)) x)) =
      exteriorPower.map 2 (Matrix.toLin' (((B5FinS8.alpha σ : ↥(StatedSL 4 (ZMod 2))) :
        Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))
        (heartEquiv (QuotientAddGroup.mk x)) := by
  rw [heartEquiv_mk, heartEquiv_mk]
  have h := B5FinS8.qHom_alt σ (Multiplicative.ofAdd (x : Fin 8 → ZMod 2))
    ((G6.mem_coreMod).2 (mem_evenWeight.mp x.2))
  have h' := congrArg Multiplicative.toAdd h
  exact h'

theorem extSqAct_one_right (γ : ↥(StatedSL 4 (ZMod 2))) :
    extSqAct (ZMod 2) 4 γ 1 = 1 := by
  simp [extSqAct]

theorem alpha_injective : Function.Injective B5FinS8.alpha := by
  intro σ τ h
  apply B5FinS8.alphaHom_bijective.1
  have h1 := congrArg B5FinS8.slEquiv h
  simpa [B5FinS8.alpha] using h1

theorem natAct_one {m : ℕ} (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin m) (ZMod 2))) (g : ↥Γ) :
    natAct Γ g 1 = 1 := by
  simp [natAct]

end T4213N

namespace Conf4212

variable {T M L I H K : Subgroup G} (c : Conf4212 G T M L I H K)
include c

theorem V_le_omega :
    ⁅reducedAggregate (L ⊔ T), L⁆ ≤ omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) := by
  have hRN : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) := by
    rw [← c.omega_eq]
    exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  rw [c.omega_eq]
  exact commutator_le_left_of_le_normalizer (le_sup_left.trans hRN)

theorem pCoreOf_le_centralizer_V {X : Subgroup G} (hX : X ≤ pCoreOf 2 (L ⊔ T)) :
    X ≤ Subgroup.centralizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) :=
  Subgroup.le_centralizer_iff.mpr (le_centralizer_of_le_omegaOneCenterOf c.V_le_omega hX)

theorem pCoreOf_L_le : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ Subgroup.normalizer (L : Set G) := c.hyp421.T_le.trans c.normal
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := _root_.sup_le Subgroup.le_normalizer hTN
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
    (hLTN.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)

theorem exists_act_L {l : G} (hl : l ∈ L) :
    ∃ a ∈ perfectCore (L ⊓ H), ∀ v ∈ ⁅reducedAggregate (L ⊔ T), L⁆, l * v * l⁻¹ = a * v * a⁻¹ := by
  have hLHO : perfectCore (L ⊓ H) ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans (le_normalizer_pCoreOf 2 L)
  obtain ⟨a, ha, o, ho, rfl⟩ := (mem_sup_of_le_normalizer hLHO).mp (c.L_le hl)
  refine ⟨a, ha, fun v hv => ?_⟩
  have hov : o * v = v * o :=
    (Subgroup.mem_centralizer_iff.mp (c.pCoreOf_le_centralizer_V c.pCoreOf_L_le ho) v hv).symm
  calc a * o * v * (a * o)⁻¹ = a * (o * v) * o⁻¹ * a⁻¹ := by group
    _ = a * v * a⁻¹ := by rw [hov]; group

theorem exists_act_sup {y : G} (hy : y ∈ perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) :
    ∃ a ∈ perfectCore (L ⊓ H), ∀ v ∈ ⁅reducedAggregate (L ⊔ T), L⁆, y * v * y⁻¹ = a * v * a⁻¹ := by
  have hRN : pCoreOf 2 I ≤ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) :=
    c.hypC28.le_M.trans c.LH_normal
  rw [sup_comm] at hy
  obtain ⟨r, hr, a, ha, rfl⟩ := (mem_sup_of_le_normalizer hRN).mp hy
  refine ⟨a, ha, fun v hv => ?_⟩
  have hav : a * v * a⁻¹ ∈ ⁅reducedAggregate (L ⊔ T), L⁆ := by
    have hLHN : perfectCore (L ⊓ H) ≤
        Subgroup.normalizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) := by
      have h1 := c.hypC28.V_comm
      rw [conjClosure_eq_self c.LH_normal] at h1
      rw [← h1]
      exact Subgroup.normalizer_commutator_ge_right _ _
    exact (Subgroup.mem_normalizer_iff.mp (hLHN ha) v).mp hv
  have hrv : r * (a * v * a⁻¹) = (a * v * a⁻¹) * r :=
    (Subgroup.mem_centralizer_iff.mp (c.pCoreOf_le_centralizer_V c.R_le hr) _ hav).symm
  calc r * a * v * (r * a)⁻¹ = r * (a * v * a⁻¹) * r⁻¹ := by group
    _ = a * v * a⁻¹ := by rw [hrv]; group

theorem autOn_eq {W : Subgroup G} (hWV : W ≤ ⁅reducedAggregate (L ⊔ T), L⁆)
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hAW : perfectCore (L ⊓ H) ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (W : Set G)) :
    autOn L W = autOn (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) W := by
  have hLHL : perfectCore (L ⊓ H) ≤ L := (perfectCore_le _).trans inf_le_left
  refine T4213N.autOn_eq_of_acts hLW hAW (fun l hl => ?_) (fun y hy => ?_)
  · obtain ⟨a, ha, hact⟩ := c.exists_act_L hl
    exact ⟨a, Subgroup.mem_sup_left ha, fun w hw => hact w (hWV hw)⟩
  · obtain ⟨a, ha, hact⟩ := c.exists_act_sup hy
    exact ⟨a, hLHL ha, fun w hw => hact w (hWV hw)⟩

theorem V_comm : ∀ a ∈ ⁅reducedAggregate (L ⊔ T), L⁆, ∀ b ∈ ⁅reducedAggregate (L ⊔ T), L⁆,
    a * b = b * a := by
  intro a ha b hb
  obtain ⟨⟨hc⟩, -⟩ := c.hypC28.V_elem
  exact congrArg Subtype.val (hc.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem isNaturalSumUnder_of_sum {m k : ℕ} (hk : 1 ≤ k)
    (hsum : IsSumOfNaturalModules (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)
      ⁅reducedAggregate (L ⊔ T), L⁆ ⊥
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) (StatedSL m (ZMod 2)) false
      k) :
    IsNaturalSumUnder m L ⁅reducedAggregate (L ⊔ T), L⁆ := by
  classical
  set LH := perfectCore (L ⊓ H) with hLHdef
  set R := pCoreOf 2 I with hRdef
  set A := LH ⊔ R with hAdef
  set V := ⁅reducedAggregate (L ⊔ T), L⁆ with hVdef
  obtain ⟨α, hα, hkerα, hAV, -, β, hβs, hβk, hβe⟩ := hsum
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  set co : Fin k → ↥V → (Fin m → ZMod 2) := fun i v => Multiplicative.toAdd (β v) i with hco
  have co_mul : ∀ i (v w : ↥V), co i (v * w) = co i v + co i w := fun i v w => by
    simp [hco]
  have co_one : ∀ i, co i 1 = 0 := fun i => by simp [hco]
  have co_inv : ∀ i (v : ↥V), co i v⁻¹ = -co i v := fun i v => by simp [hco]
  have co_ext : ∀ v w : ↥V, (∀ i, co i v = co i w) → v = w := fun v w h => by
    apply hβi
    apply Multiplicative.toAdd.injective
    funext i
    exact h i
  have co_act : ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * (a : G)⁻¹ → ∀ i,
      co i v = ((α a : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) : Matrix _ _ (ZMod 2)).mulVec
        (co i u) := fun a u v huv i => by
    have h := hβe a u v huv i
    simpa [moduleAct] using h
  let S : Fin k → Subgroup ↥V := fun i =>
    { carrier := {v | ∀ j, j ≠ i → co j v = 0}
      mul_mem' := fun {v w} hv hw j hj => by rw [co_mul, hv j hj, hw j hj, add_zero]
      one_mem' := fun j _ => co_one j
      inv_mem' := fun {v} hv j hj => by rw [co_inv, hv j hj, neg_zero] }
  set W : Fin k → Subgroup G := fun i => (S i).map V.subtype with hWdef
  have hWV : ∀ i, W i ≤ V := fun i => Subgroup.map_subtype_le _
  have mem_W : ∀ i {x : G} (hx : x ∈ V), x ∈ W i ↔ (⟨x, hx⟩ : ↥V) ∈ S i := fun i x hx =>
    ⟨fun ⟨v, hv, hvx⟩ => by
      have : v = ⟨x, hx⟩ := Subtype.ext hvx
      rwa [← this], fun h => ⟨⟨x, hx⟩, h, rfl⟩⟩
  have hAV' : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V := fun a ha v hv =>
    (Subgroup.mem_normalizer_iff.mp (hAV ha) v).mp hv
  have hAW : ∀ i, A ≤ Subgroup.normalizer (W i : Set G) := by
    intro i a ha
    refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
    have hwV := hWV i hw
    rw [mem_W i (hAV' a ha w hwV)]
    intro j hj
    rw [co_act ⟨a, ha⟩ ⟨w, hwV⟩ _ rfl j, (mem_W i hwV).mp hw j hj, Matrix.mulVec_zero]
  have hLW : ∀ i, L ≤ Subgroup.normalizer (W i : Set G) := by
    intro i l hl
    obtain ⟨a, ha, hact⟩ := c.exists_act_L hl
    refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
    rw [hact w (hWV i hw)]
    exact (Subgroup.mem_normalizer_iff.mp (hAW i (Subgroup.mem_sup_left ha)) w).mp hw
  have hcomm : ∀ i, IsMulCommutative ↥(W i) := fun i =>
    ⟨⟨fun a b => Subtype.ext (c.V_comm _ (hWV i a.2) _ (hWV i b.2))⟩⟩
  let g : ∀ i, ↥(S i) →* Multiplicative (Fin m → ZMod 2) := fun i =>
    { toFun := fun v => Multiplicative.ofAdd (co i v)
      map_one' := by
        show Multiplicative.ofAdd (co i 1) = 1
        rw [co_one]
        rfl
      map_mul' := fun v w => by
        show Multiplicative.ofAdd (co i (v * w)) = _
        rw [co_mul]
        rfl }
  have hg_bij : ∀ i, Function.Bijective (g i) := by
    intro i
    refine ⟨fun v w hvw => ?_, fun y => ?_⟩
    · have h1 : co i v = co i w := congrArg Multiplicative.toAdd hvw
      apply Subtype.ext
      refine co_ext _ _ fun j => ?_
      rcases eq_or_ne j i with rfl | hji
      · exact h1
      · rw [v.2 j hji, w.2 j hji]
    · obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd y)))
      have huc : ∀ j, co j u =
          (Pi.single i (Multiplicative.toAdd y) : Fin k → Fin m → ZMod 2) j := fun j => by
        rw [hco]
        simp only [hu, toAdd_ofAdd]
      refine ⟨⟨u, fun j hj => by rw [huc, Pi.single_eq_of_ne hj]⟩, ?_⟩
      show Multiplicative.ofAdd (co i u) = y
      rw [huc, Pi.single_eq_same, ofAdd_toAdd]
  let f : ∀ i, ↥(W i) ≃* Multiplicative (Fin m → ZMod 2) := fun i =>
    (Subgroup.equivMapOfInjective (S i) V.subtype V.subtype_injective).symm.trans
      (MulEquiv.ofBijective (g i) (hg_bij i))
  have hf_apply : ∀ i (w : ↥(W i)), f i w = Multiplicative.ofAdd (co i ⟨w, hWV i w.2⟩) := by
    intro i w
    set v := (Subgroup.equivMapOfInjective (S i) V.subtype V.subtype_injective).symm w with hv
    have hvw : ((v : ↥V) : G) = w := by
      have h1 :=
        (Subgroup.equivMapOfInjective (S i) V.subtype V.subtype_injective).apply_symm_apply w
      rw [← hv] at h1
      exact congrArg Subtype.val h1
    have hv' : (v : ↥V) = ⟨w, hWV i w.2⟩ := Subtype.ext hvw
    show Multiplicative.ofAdd (co i (v : ↥V)) = _
    rw [hv']
  have hfeq : ∀ i (a : ↥A) (w w' : ↥(W i)), (w' : G) = a * w * (a : G)⁻¹ →
      f i w' = natAct (StatedSL m (ZMod 2)) (α a) (f i w) := by
    intro i a w w' hw'
    rw [hf_apply, hf_apply]
    unfold natAct
    rw [toAdd_ofAdd, co_act a ⟨w, hWV i w.2⟩ ⟨w', hWV i w'.2⟩ hw' i]
  have hker : ∀ a : ↥A, α a = 1 →
      (a : G) ∈ Subgroup.centralizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) := by
    intro a ha
    have h1 : a ∈ α.ker := ha
    rw [hkerα, Subgroup.mem_subgroupOf] at h1
    exact c.pCoreOf_le_centralizer_V c.R_le h1
  have hreal : ∀ i, (FFModel.nat (StatedSL m (ZMod 2))).Realizes (autOn L (W i)) ⊤ ⊥ := by
    intro i
    have := hcomm i
    rw [c.autOn_eq (hWV i) (hLW i) (hAW i)]
    exact T4213N.realizes_of_equiv (hAW i) (FFModel.nat (StatedSL m (ZMod 2))) (fun _ => trivial)
      (fun _ => Subgroup.mem_bot)
      (fun γ => T4213N.natAct_one _ γ) α hα
      (fun a ha => Subgroup.centralizer_le (hWV i) (hker a ha)) (f i) (hfeq i)
  have hiso : ∀ i j, IsXSectionIso₂ L (W i) ⊥ (W j) ⊥ := by
    intro i j
    refine isXSectionIso₂_of_isLEquiv (φ := (f i).trans (f j).symm) ?_
    intro l hl a a' ha'
    obtain ⟨x, hx, hact⟩ := c.exists_act_L hl
    set b := ((f i).trans (f j).symm) a with hb
    have hbW : l * (b : G) * l⁻¹ ∈ W j := (Subgroup.mem_normalizer_iff.mp (hLW j hl) b).mp b.2
    have hfb : f j b = f i a := by
      show f j ((f j).symm (f i a)) = f i a
      exact MulEquiv.apply_symm_apply _ _
    have h1 : f j ⟨l * b * l⁻¹, hbW⟩ = f i a' := by
      have e1 := hfeq j ⟨x, Subgroup.mem_sup_left hx⟩ b ⟨l * b * l⁻¹, hbW⟩
        (hact b (hWV j b.2))
      have e2 := hfeq i ⟨x, Subgroup.mem_sup_left hx⟩ a a'
        (by rw [ha']; exact hact a (hWV i a.2))
      rw [e1, e2, hfb]
    have h2 : ((f i).trans (f j).symm) a' = ⟨l * b * l⁻¹, hbW⟩ := by
      rw [MulEquiv.trans_apply, ← h1, MulEquiv.symm_apply_apply]
    rw [h2]
  have hind : iSupIndep W := by
    rw [iSupIndep_def]
    intro i
    rw [Subgroup.disjoint_def]
    intro x hxi hxj
    have hxV := hWV i hxi
    let P : Subgroup ↥V :=
      { carrier := {v | co i v = 0}
        mul_mem' := fun {v w} hv hw => by
          show co i (v * w) = 0
          rw [co_mul, hv, hw, add_zero]
        one_mem' := co_one i
        inv_mem' := fun {v} hv => by
          show co i v⁻¹ = 0
          rw [co_inv, hv, neg_zero] }
    have hle : (⨆ (j) (_ : j ≠ i), W j) ≤ P.map V.subtype := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, hv i (Ne.symm hj), rfl⟩
    obtain ⟨v, hvP, hvx⟩ := hle hxj
    have hv : v = ⟨x, hxV⟩ := Subtype.ext hvx
    subst hv
    have h1 : (⟨x, hxV⟩ : ↥V) = 1 := co_ext _ _ fun j => by
      rw [co_one]
      rcases eq_or_ne j i with rfl | hji
      · exact hvP
      · exact (mem_W i hxV).mp hxi j hji
    exact congrArg Subtype.val h1
  have hsup : ⨆ i, W i = V := by
    refine le_antisymm (iSup_le hWV) fun x hx => ?_
    set Q : Subgroup ↥V := (⨆ i, W i).comap V.subtype with hQdef
    have hQ : Q.map β = ⊤ := by
      rw [eq_top_iff]
      rintro y -
      have hy : y = ∏ j, Multiplicative.ofAdd
          ((Pi.single j (Multiplicative.toAdd y j) : Fin k → Fin m → ZMod 2)) := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_prod]
        simp only [toAdd_ofAdd]
        exact (Finset.univ_sum_single (Multiplicative.toAdd y)).symm
      rw [hy]
      refine Subgroup.prod_mem _ fun j _ => ?_
      obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd
        ((Pi.single j (Multiplicative.toAdd y j) : Fin k → Fin m → ZMod 2)))
      have huS : u ∈ S j := fun j' hj' => by
        rw [hco]
        simp only [hu, toAdd_ofAdd]
        exact Pi.single_eq_of_ne hj' _
      exact ⟨u, Subgroup.mem_iSup_of_mem j ⟨u, huS, rfl⟩, hu⟩
    have hQt : Q = ⊤ :=
      Subgroup.map_injective hβi (hQ.trans (Subgroup.map_top_of_surjective β hβs).symm)
    have hxQ : (⟨x, hx⟩ : ↥V) ∈ Q := hQt ▸ Subgroup.mem_top _
    exact hxQ
  exact ⟨k, W, hk, fun i => ⟨hWV i, hLW i, hcomm i,
    ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, hreal i⟩⟩,
    hiso, hind, hsup⟩

theorem L_le_normalizer_V :
    L ≤ Subgroup.normalizer ((⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) : Set G) := by
  have hRN : L ⊔ T ≤ Subgroup.normalizer (reducedAggregate (L ⊔ T) : Set G) := by
    rw [← c.omega_eq]
    exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  exact fun l hl => mem_normalizer_commutator (hRN (Subgroup.mem_sup_left hl))
    (Subgroup.le_normalizer hl)

theorem slExteriorTwo_of_alt
    (halt : IsAltNaturalSection (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆
      ⊥ ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I)) 8) :
    ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
      SLExteriorTwo (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
        (autOn L ⁅reducedAggregate (L ⊔ T), L⁆) ⊤ ⊥ 4 := by
  set LH := perfectCore (L ⊓ H) with hLHdef
  set R := pCoreOf 2 I with hRdef
  set A := LH ⊔ R with hAdef
  set V := ⁅reducedAggregate (L ⊔ T), L⁆ with hVdef
  obtain ⟨hAV, α₀, hα₀, hker₀, β₀, hβs, hβk, hβe⟩ := halt
  have hβi : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have hcomm : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (c.V_comm _ a.2 _ b.2)⟩⟩
  let f : ↥V ≃* Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)) :=
    (MulEquiv.ofBijective β₀ ⟨hβi, hβs⟩).trans (AddEquiv.toMultiplicative T4213N.heartEquiv)
  have hfeq : ∀ (a : ↥A) (w w' : ↥V), (w' : G) = a * w * (a : G)⁻¹ →
      f w' = extSqAct (ZMod 2) 4 ((B5FinS8.alpha.comp α₀) a) (f w) := by
    intro a w w' hw'
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β₀ w))
    have h1 := hβe a w w' hw' x hx
    show Multiplicative.ofAdd (T4213N.heartEquiv (Multiplicative.toAdd (β₀ w'))) =
      extSqAct (ZMod 2) 4 (B5FinS8.alpha (α₀ a))
        (Multiplicative.ofAdd (T4213N.heartEquiv (Multiplicative.toAdd (β₀ w))))
    rw [← h1, ← hx, T4213N.heartEquiv_perm]
    rfl
  have hker : ∀ a : ↥A, (B5FinS8.alpha.comp α₀) a = 1 →
      (a : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro a ha
    have h1 : α₀ a = 1 :=
      T4213N.alpha_injective (by rw [MonoidHom.comp_apply] at ha; rw [ha, map_one])
    have h2 : a ∈ α₀.ker := h1
    rw [hker₀, Subgroup.mem_subgroupOf] at h2
    exact c.pCoreOf_le_centralizer_V c.R_le h2
  refine ⟨hcomm, ?_⟩
  unfold SLExteriorTwo
  rw [c.autOn_eq le_rfl c.L_le_normalizer_V hAV]
  exact T4213N.realizes_of_equiv hAV (FFModel.extSq (ZMod 2) 4) (fun _ => trivial)
    (fun _ => Subgroup.mem_bot) T4213N.extSqAct_one_right (B5FinS8.alpha.comp α₀)
    (B5FinS8.alpha_surjective.comp hα₀) hker f hfeq

end Conf4212

end CFSG.Quasithin.H13.Ch4
