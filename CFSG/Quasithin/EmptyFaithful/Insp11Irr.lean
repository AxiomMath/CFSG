module

public import CFSG.Quasithin.EmptyFaithful.Insp11Rho
public import CFSG.Quasithin.EmptyFaithful.Insp11NP

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

@[expose] def IrrModShape : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H : Subgroup (MulAut V), H ≠ ⊥ → B53Hyp H → commV H = ⊤ → IsInspList ↥H →
      ¬ Nonempty (↥H ≃* Equiv.Perm (Fin 3)) →
      (∀ U : Subgroup V, XMod.IsInv ↥H U → U ≤ fixV H ∨ U ⊔ fixV H = ⊤) ∨
        Nonempty (↥H ≃* ↥(StatedSL 3 (ZMod 2)))

namespace Insp11

section Transport

theorem isInspList_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsInspList X) :
    IsInspList Y := by
  unfold IsInspList at h ⊢
  rcases h with a | a | a | a | a | hH | a | a
  · obtain ⟨a⟩ := a
    exact Or.inl ⟨e.symm.trans a⟩
  · obtain ⟨a⟩ := a
    exact Or.inr (Or.inl ⟨e.symm.trans a⟩)
  · obtain ⟨a⟩ := a
    exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans a⟩))
  · obtain ⟨a⟩ := a
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans a⟩)))
  · obtain ⟨a⟩ := a
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans a⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Insp9.isHatAlt_of_mulEquiv e hH))))))
  · obtain ⟨a⟩ := a
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans a⟩))))))
  · obtain ⟨a⟩ := a
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans a⟩))))))

end Transport

section Action

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem YF_act (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s)
    (hO2 : oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸
        CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≤ Xdot153 T Mc M E s) :
    ∀ y ∈ YF153 Mc M E s, ∃ x ∈ thompsonJ (G0_153 T Mc M E s),
      ∀ u ∈ V0_153 T Mc M E s, y * u * y⁻¹ = x * u * x⁻¹ := by
  classical
  have hYFI : YF153 Mc M E s ≤ G0_153 T Mc M E s := le_sup_left.trans le_sup_left
  have hVN : G0_153 T Mc M E s ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := V0_normal
  have hJle := B6.thompsonJ_le (G0_153 T Mc M E s)
  have hcard := S1567.card_mulAut_quot_YE h113 c L r66
  have hJα := thompsonJ_G0_le_ker_alpha c L r66 r67 gl r68
  let S : Subgroup G :=
    { carrier := {y | y ∈ G0_153 T Mc M E s ∧ ∃ x ∈ thompsonJ (G0_153 T Mc M E s),
        ∀ u ∈ V0_153 T Mc M E s, y * u * y⁻¹ = x * u * x⁻¹}
      one_mem' := ⟨(G0_153 T Mc M E s).one_mem, 1, (thompsonJ _).one_mem, fun u _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haI, xa, hxa, ha⟩ ⟨hbI, xb, hxb, hb⟩
        refine ⟨(G0_153 T Mc M E s).mul_mem haI hbI, xa * xb, (thompsonJ _).mul_mem hxa hxb,
          fun u hu => ?_⟩
        have hxbI : xb ∈ G0_153 T Mc M E s := hJle hxb
        have hmem : xb * u * xb⁻¹ ∈ V0_153 T Mc M E s :=
          (Subgroup.mem_normalizer_iff.mp (hVN hxbI) u).mp hu
        calc a * b * u * (a * b)⁻¹ = a * (b * u * b⁻¹) * a⁻¹ := by group
          _ = a * (xb * u * xb⁻¹) * a⁻¹ := by rw [hb u hu]
          _ = xa * (xb * u * xb⁻¹) * xa⁻¹ := ha _ hmem
          _ = xa * xb * u * (xa * xb)⁻¹ := by group
      inv_mem' := by
        rintro a ⟨haI, x, hx, ha⟩
        refine ⟨(G0_153 T Mc M E s).inv_mem haI, x⁻¹, (thompsonJ _).inv_mem hx, fun u hu => ?_⟩
        have hmem : a⁻¹ * u * a ∈ V0_153 T Mc M E s := by
          have := (Subgroup.mem_normalizer_iff.mp (hVN ((G0_153 T Mc M E s).inv_mem haI)) u).mp hu
          simpa using this
        have h1 := ha _ hmem
        have h2 : u = x * (a⁻¹ * u * a) * x⁻¹ := by
          rw [← h1]
          group
        have h3 : x⁻¹ * u * x = a⁻¹ * u * a := by
          calc x⁻¹ * u * x = x⁻¹ * (x * (a⁻¹ * u * a) * x⁻¹) * x := by rw [← h2]
            _ = a⁻¹ * u * a := by group
        calc a⁻¹ * u * a⁻¹⁻¹ = a⁻¹ * u * a := by group
          _ = x⁻¹ * u * x⁻¹⁻¹ := by rw [← h3]; group }
  have hSle : YF153 Mc M E s ≤ S := by
    rw [← oTwoUpper_YF Mc M E s]
    refine (Subgroup.closure_le S).mpr fun y hy => ?_
    have hyI : y ∈ G0_153 T Mc M E s := hYFI hy.1
    have hodd : Odd (orderOf (QuotientGroup.mk ⟨y, hyI⟩ : ↥(G0_153 T Mc M E s) ⧸
        CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) := by
      refine Odd.of_dvd_nat (n := orderOf y) hy.2 ?_
      have := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))
        (⟨y, hyI⟩ : ↥(G0_153 T Mc M E s))
      rwa [Subgroup.orderOf_mk] at this
    have hX := hO2 (mem_oTwoUpper_of_odd (Subgroup.mem_top _) hodd)
    obtain ⟨x, hxX, hxu⟩ := mem_barQ.mp hX
    have h1 : x⁻¹ * ⟨y, hyI⟩ ∈ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) := QuotientGroup.eq.mp hxu
    have hq : (x : G)⁻¹ * y ∈ pCoreOf 2 (G0_153 T Mc M E s) := by
      rw [r68.pCore_eq]
      exact ⟨x⁻¹ * ⟨y, hyI⟩, h1, by simp⟩
    have hqG : (x : G)⁻¹ * y ∈ G0_153 T Mc M E s :=
      (G0_153 T Mc M E s).mul_mem ((G0_153 T Mc M E s).inv_mem x.2) hyI
    have hαy : S1567.alpha153 T Mc M E s r68.le_normalizer ⟨y, hyI⟩ = 1 := by
      refine S1567.eq_one_of_odd_of_card_two hcard
        (S1567.alpha153 T Mc M E s r68.le_normalizer) ?_
      rw [Subgroup.orderOf_mk]
      exact hy.2
    have hαx : S1567.alpha153 T Mc M E s r68.le_normalizer x = 1 := by
      obtain ⟨z, hz, hzx⟩ := hJα hxX
      have : z = x := Subtype.ext hzx
      subst this
      exact hz
    have hα : S1567.alpha153 T Mc M E s r68.le_normalizer ⟨(x : G)⁻¹ * y, hqG⟩ = 1 := by
      have e : (⟨(x : G)⁻¹ * y, hqG⟩ : ↥(G0_153 T Mc M E s)) = x⁻¹ * ⟨y, hyI⟩ := rfl
      rw [e, map_mul, map_inv, hαx, hαy]
      simp
    have hC := pCore_inf_ker_alpha_le_centralizer_V0_NR h113 c L r66 r67 gl r68 hq hqG hα
    refine ⟨hyI, x, hxX, fun u hu => ?_⟩
    have hqu : u * ((x : G)⁻¹ * y) = ((x : G)⁻¹ * y) * u := Subgroup.mem_centralizer_iff.mp hC u hu
    calc y * u * y⁻¹ = (x : G) * (((x : G)⁻¹ * y) * u * ((x : G)⁻¹ * y)⁻¹) * (x : G)⁻¹ := by group
      _ = (x : G) * u * (x : G)⁻¹ := by
        rw [← hqu]
        group
  exact fun y hy => (hSle hy).2

theorem commutator_V0_thompsonJ (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s)
    (hO2 : oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸
        CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≤ Xdot153 T Mc M E s) :
    ⁅V0_153 T Mc M E s, thompsonJ (G0_153 T Mc M E s)⁆ = V0_153 T Mc M E s := by
  classical
  have hVN : G0_153 T Mc M E s ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := V0_normal
  have hJle := B6.thompsonJ_le (G0_153 T Mc M E s)
  have hJN := B6.le_normalizer_thompsonJ (G0_153 T Mc M E s)
  have hcomm := commutator_VZ_YF c r66 gl
  have hact := YF_act h113 c L r66 r67 gl r68 hO2
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro u hu x hx
    have hxu : x * u⁻¹ * x⁻¹ ∈ V0_153 T Mc M E s :=
      (Subgroup.mem_normalizer_iff.mp (hVN (hJle hx)) u⁻¹).mp ((V0_153 T Mc M E s).inv_mem hu)
    have e : ⁅u, x⁆ = u * (x * u⁻¹ * x⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (V0_153 T Mc M E s).mul_mem hu hxu
  · set K := ⁅V0_153 T Mc M E s, thompsonJ (G0_153 T Mc M E s)⁆ with hK
    have hKN : ∀ g ∈ G0_153 T Mc M E s, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
      intro g hg k hk
      rw [hK, Subgroup.commutator_def] at hk
      refine Subgroup.closure_induction (p := fun k _ => g * k * g⁻¹ ∈ K) ?_ ?_ ?_ ?_ hk
      · rintro _ ⟨u, hu, x, hx, rfl⟩
        have hu' : g * u * g⁻¹ ∈ V0_153 T Mc M E s :=
          (Subgroup.mem_normalizer_iff.mp (hVN hg) u).mp hu
        have hx' : g * x * g⁻¹ ∈ thompsonJ (G0_153 T Mc M E s) :=
          (Subgroup.mem_normalizer_iff.mp (hJN hg) x).mp hx
        have e : g * ⁅u, x⁆ * g⁻¹ = ⁅g * u * g⁻¹, g * x * g⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.commutator_mem_commutator hu' hx'
      · simp
      · intro a b _ _ ha hb
        have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [e]
        exact K.mul_mem ha hb
      · intro a _ ha
        have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [e]
        exact K.inv_mem ha
    have hVK : VZ T M ≤ K := by
      rw [← hcomm]
      rw [Subgroup.commutator_le]
      intro v hv y hy
      obtain ⟨x, hx, hxy⟩ := hact y hy
      have hvV0 : v ∈ V0_153 T Mc M E s := V_le_V0 hv
      have e : ⁅v, y⁆ = ⁅v, x⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        have h1 := hxy v⁻¹ ((V0_153 T Mc M E s).inv_mem hvV0)
        calc v * y * v⁻¹ * y⁻¹ = v * (y * v⁻¹ * y⁻¹) := by group
          _ = v * (x * v⁻¹ * x⁻¹) := by rw [h1]
          _ = v * x * v⁻¹ * x⁻¹ := by group
      rw [e]
      exact Subgroup.commutator_mem_commutator hvV0 hx
    exact conjClosure_le fun g hg z hz => hKN g hg z (hVK hz)

end Action

section Main

theorem inspectIrrShapeL3_of_mod (h113 : StageLemma14113) (hM : IrrModShape) :
    InspectIrrShapeL3 := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc hlist hS3 hO2
  classical
  have hV0 : IsElemAbelian 2 (V0_153 T Mc M E s) := isElemAbelian_V0_NoTwo c r46 L r66 r67 gl r68
  have hIN : G0_153 T Mc M E s ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := V0_normal
  have hVI : V0_153 T Mc M E s ≤ G0_153 T Mc M E s := V0_le_G0_NT r68
  obtain ⟨ρ, hρ, hρα⟩ := exists_faithful_rho_NR h113 c r46 L r66 r67 gl r68
  have hJα : ∀ g : ↥(G0_153 T Mc M E s), (g : G) ∈ thompsonJ (G0_153 T Mc M E s) →
      S1567.alpha153 T Mc M E s r68.le_normalizer g = 1 := by
    intro g hg
    obtain ⟨y, hy, hyg⟩ := thompsonJ_G0_le_ker_alpha c L r66 r67 gl r68 hg
    have : y = g := Subtype.ext hyg
    subst this
    exact hy
  have hA : IsGoldschmidtAmalgam
      (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G1_153 T Mc M E s))
      (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G2_153 T E)) := by
    rcases r68.triple.goldschmidt_mod_pPrimeCore with ⟨-, hA, -⟩ | ⟨-, -, -, -, hcyc⟩
    · exact hA
    · exfalso
      apply hcyc
      have hpc : Open.pCore 2 ↥(G0_153 T Mc M E s) = CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) :=
        Subgroup.map_injective (G0_153 T Mc M E s).subtype_injective r68.pCore_eq
      have hbot : (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (Open.pCore 2 ↥(G0_153 T Mc M E s))) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', hpc]
      rw [hbot]
      infer_instance
  have hD : Open.pCore 2 (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) = ⊥ :=
    hA.pCore_eq_bot
  have hSQ : SQTKGroup ↥(G0_153 T Mc M E s) := sqtkGroup_G0_NT c r68
  have hB53 := b53Hyp_autI_thompsonJ_of_faithful hV0 hIN hVI _ ρ hρ
    (fun g => S1567.alpha153 T Mc M E s r68.le_normalizer g = 1) hρα hJα hD
    (sqtkGroup_of_le hSQ (B6.thompsonJ_le _))
  have hmapN := map_barQ_eq_autI hV0 hIN _ ρ
    (fun g => S1567.alpha153 T Mc M E s r68.le_normalizer g = 1) hρα
    (B6.thompsonJ_le (G0_153 T Mc M E s)) hJα
  have hXI : XE153 E ≤ G0_153 T Mc M E s :=
    (le_sup_left : XE153 E ≤ G2_153 T E).trans le_sup_right
  have hXEJ := XE_le_thompsonJ_NT c L r66 r67 gl r68
  have hne : autI hV0 (thompsonJ (G0_153 T Mc M E s)) ≠ ⊥ := by
    rw [← hmapN]
    intro h
    have h' := (Subgroup.map_eq_bot_iff_of_injective _ hρ).mp h
    exact barQ_XE_ne_bot_NT r67 r68 hXI (le_bot_iff.mp ((barQ_mono hXEJ).trans h'.le))
  have hJN : thompsonJ (G0_153 T Mc M E s) ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) :=
    (B6.thompsonJ_le _).trans hIN
  have hcomm : commV (autI hV0 (thompsonJ (G0_153 T Mc M E s))) = ⊤ := by
    have h1 := S1417.commutator_eq_map_commV hV0 hJN
    have h2 := commutator_V0_thompsonJ h113 c L r66 r67 gl r68 hO2
    apply Subgroup.map_injective (S1417.inclMod_injective hV0)
    rw [← h1, S1417.map_inclMod_top hV0]
    exact h2
  have eH : ↥(Xdot153 T Mc M E s) ≃* ↥(autI hV0 (thompsonJ (G0_153 T Mc M E s))) :=
    (Subgroup.equivMapOfInjective _ ρ hρ).trans (MulEquiv.subgroupCongr hmapN)
  have hlistH : IsInspList ↥(autI hV0 (thompsonJ (G0_153 T Mc M E s))) :=
    isInspList_of_mulEquiv eH hlist
  have hS3H : ¬ Nonempty (↥(autI hV0 (thompsonJ (G0_153 T Mc M E s))) ≃* Equiv.Perm (Fin 3)) :=
    fun ⟨e⟩ => hS3 ⟨eH.trans e⟩
  rcases hM (IntMod (V0_153 T Mc M E s) hV0) (fun v => IntMod.sq_eq_one v)
    (autI hV0 (thompsonJ (G0_153 T Mc M E s))) hne hB53 hcomm hlistH hS3H with hirr | he
  · left
    intro U hUV hUinv
    let U' : Subgroup (IntMod (V0_153 T Mc M E s) hV0) := U.comap (S1417.inclMod hV0)
    have hU'inv : XMod.IsInv ↥(autI hV0 (thompsonJ (G0_153 T Mc M E s))) U' := by
      intro φ u hu
      obtain ⟨g, hg, hgφ⟩ := (mem_autI hV0).mp φ.2
      show (φ : MulAut _) u ∈ U'
      rw [← hgφ]
      show S1417.inclMod hV0 (convI hV0 g u) ∈ U
      rw [S1417.inclMod_apply, convI_apply_val]
      have hu'' : u.val ∈ U := by
        have := (Subgroup.mem_comap.mp hu : S1417.inclMod hV0 u ∈ U)
        rwa [S1417.inclMod_apply] at this
      exact hUinv _ hg _ hu''
    rcases hirr U' hU'inv with h | h
    · left
      intro u hu
      have hu' : IntMod.mk hV0 ⟨u, hUV hu⟩ ∈ U' := by
        show S1417.inclMod hV0 (IntMod.mk hV0 ⟨u, hUV hu⟩) ∈ U
        rw [S1417.inclMod_apply]
        exact hu
      have := h hu'
      rw [mem_fixV_autI hV0 hJN] at this
      exact this
    · right
      intro v hv
      have hmem : IntMod.mk hV0 ⟨v, hv⟩ ∈
          U' ⊔ fixV (autI hV0 (thompsonJ (G0_153 T Mc M E s))) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hmem
      have ha' : a.val ∈ U := by
        have := (Subgroup.mem_comap.mp ha : S1417.inclMod hV0 a ∈ U)
        rwa [S1417.inclMod_apply] at this
      refine ⟨a.val, ha', ?_⟩
      have hb' : b.val ∈ Subgroup.centralizer (thompsonJ (G0_153 T Mc M E s) : Set G) :=
        (mem_fixV_autI hV0 hJN b).mp hb
      have hv' : a.val * b.val = v := congrArg IntMod.val hab
      have e : a.val⁻¹ * v = b.val := by
        rw [← hv']
        group
      rw [e]
      exact hb'
  · right
    obtain ⟨e⟩ := he
    exact ⟨eH.trans e⟩

end Main

end Insp11

theorem inspectRemainingNP_of_inputs₄ (h113 : StageLemma14113)
    (hI : IrrModShape) (hB : InspectB51Rem153) (hG : A5HatGeom153) : InspectRemainingNP :=
  inspectRemainingNP_of_inputs₃ h113 (Insp11.inspectIrrShapeL3_of_mod h113 hI) hB hG


end CFSG.Quasithin
