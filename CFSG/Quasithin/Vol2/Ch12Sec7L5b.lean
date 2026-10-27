module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5a
public import CFSG.Quasithin.Background.SmithC27OTwoZ
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13.S127.L5

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_coset {V Z : Subgroup G} (hc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {R : Subgroup (MulAut ↥V)} (hR : IsPGroup 2 ↥R)
    (hRZ : ∀ r ∈ R, ∀ z : ↥V, (z : G) ∈ Z → ((r z : ↥V) : G) ∈ Z)
    (hQ : 2 ∣ Nat.card (↥V ⧸ Z.subgroupOf V)) :
    ∃ v : ↥V, (v : G) ∉ Z ∧ ∀ r ∈ R, ((r v : ↥V) : G) * (v : G)⁻¹ ∈ Z := by
  classical
  set Z' : Subgroup ↥V := Z.subgroupOf V with hZ'
  have hcomm : ∀ a b : ↥V, a * b = b * a := fun a b => Subtype.ext (hc a a.2 b b.2)
  have : Z'.Normal := ⟨fun n hn g => by
    rw [hcomm g n, mul_inv_cancel_right]
    exact hn⟩
  have hle : ∀ r : ↥R, Z' ≤ Z'.comap (r : MulAut ↥V).toMonoidHom := fun r z hz =>
    hRZ r r.2 z hz
  let _ : MulAction ↥R (↥V ⧸ Z') :=
    { smul := fun r q => QuotientGroup.map Z' Z' (r : MulAut ↥V).toMonoidHom (hle r) q
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on with
        | H x => rfl
      mul_smul := fun r s q => by
        induction q using QuotientGroup.induction_on with
        | H x => rfl }
  have hsmul : ∀ (r : ↥R) (x : ↥V), r • (x : ↥V ⧸ Z') = ((r : MulAut ↥V) x : ↥V ⧸ Z') :=
    fun _ _ => rfl
  have hmod := hR.card_modEq_card_fixedPoints (α := ↥V ⧸ Z')
  have h1fix : (1 : ↥V ⧸ Z') ∈ MulAction.fixedPoints ↥R (↥V ⧸ Z') := by
    intro r
    show r • ((1 : ↥V) : ↥V ⧸ Z') = ((1 : ↥V) : ↥V ⧸ Z')
    rw [hsmul, map_one]
  obtain ⟨q, hq, hq1⟩ : ∃ q ∈ MulAction.fixedPoints ↥R (↥V ⧸ Z'), q ≠ 1 := by
    by_contra hno
    push Not at hno
    have hsub : MulAction.fixedPoints ↥R (↥V ⧸ Z') = {1} := by
      ext q
      exact ⟨fun hq => hno q hq, fun hq => hq ▸ h1fix⟩
    have hcard : Nat.card (MulAction.fixedPoints ↥R (↥V ⧸ Z')) = 1 := by
      rw [hsub]
      simp
    rw [hcard] at hmod
    unfold Nat.ModEq at hmod
    have := Nat.mod_eq_zero_of_dvd hQ
    omega
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨v, fun hvZ => hq1 ((QuotientGroup.eq_one_iff _).mpr hvZ), fun r hr => ?_⟩
  have hfix := hq ⟨r, hr⟩
  rw [hsmul] at hfix
  have h4 : (r v)⁻¹ * v ∈ Z' := QuotientGroup.eq.mp hfix
  have h5 := Z.inv_mem (Subgroup.mem_subgroupOf.mp h4)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
  rw [mul_inv_rev, inv_inv] at h5
  rw [hc _ (r v).2 _ (V.inv_mem v.2)]
  exact h5

omit [Finite G] in
theorem normalizer_le_normalizer_XOf (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (XOf L : Set G) :=
  (SmithC27.normalizer_le_normalizer_oTwoZIn L).trans (normalizer_le_normalizer_oTwoUpper _)

theorem mem_normalizer_Vt {L : Subgroup G} {t a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) :
    a ∈ Subgroup.normalizer (Vt L t : Set G) := by
  have hX := normalizer_le_normalizer_XOf L ha
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  have hle : Vt L t ≤ (Vt L t).comap (MulAut.conj a).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, hx, z, hz, rfl⟩
    have hza : a * z * a⁻¹ = z := by
      obtain ⟨k, rfl⟩ := hz
      have hc : Commute a t := Subgroup.mem_centralizer_singleton_iff.mp hat
      simp only [(hc.zpow_right k).eq, mul_inv_cancel_right]
    have hax : a * x * a⁻¹ ∈ XOf L := (Subgroup.mem_normalizer_iff.mp hX x).mp hx
    refine Subgroup.subset_closure ⟨_, hax, z, hz, ?_⟩
    show a * x * a⁻¹ * z * (a * x * a⁻¹)⁻¹ = a * (x * z * x⁻¹) * a⁻¹
    conv_lhs => rw [← hza]
    group
  exact hle hv

variable {T L V : Subgroup G} {t : G}

namespace D127

variable (d : D127 G T L V t)
include d

theorem card_quot : Nat.card (↥V ⧸ (Vt L t).subgroupOf V) = 16 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((Vt L t).subgroupOf V)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.vt_le).toEquiv, d.card_Vt, d.card_V] at h1
  omega

theorem lt_le_normalizer : Lt L t ≤ Subgroup.normalizer (V : Set G) :=
  (d.lt_le.trans inf_le_left).trans (le_normalizer_V d.hyp)

theorem trivial_mod_Vt {R : Subgroup (MulAut ↥V)} (hR : IsPGroup 2 ↥R)
    (hRVt : ∀ r ∈ R, ∀ v : ↥V, (v : G) ∈ Vt L t → ((r v : ↥V) : G) ∈ Vt L t)
    (hRn : autOn (Lt L t) V ≤ Subgroup.normalizer (R : Set (MulAut ↥V))) :
    ∀ r ∈ R, ∀ v : ↥V, ((r v : ↥V) : G) * (v : G)⁻¹ ∈ Vt L t := by
  have hcV := d.comm
  let W : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ V, ∀ r ∈ R, ((r ⟨g, hg⟩ : ↥V) : G) * g⁻¹ ∈ Vt L t}
      mul_mem' := by
        rintro a b ⟨ha, hra⟩ ⟨hb, hrb⟩
        refine ⟨V.mul_mem ha hb, fun r hr => ?_⟩
        have e : ((r ⟨a * b, V.mul_mem ha hb⟩ : ↥V) : G) * (a * b)⁻¹ =
            (((r ⟨a, ha⟩ : ↥V) : G) * a⁻¹) * (((r ⟨b, hb⟩ : ↥V) : G) * b⁻¹) := by
          have hm : (⟨a * b, V.mul_mem ha hb⟩ : ↥V) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
          rw [hm, map_mul, Subgroup.coe_mul, mul_inv_rev]
          have hc1 := hcV _ (V.inv_mem ha) _ (V.mul_mem (r ⟨b, hb⟩).2 (V.inv_mem hb))
          calc ((r ⟨a, ha⟩ : ↥V) : G) * ((r ⟨b, hb⟩ : ↥V) : G) * (b⁻¹ * a⁻¹)
              = ((r ⟨a, ha⟩ : ↥V) : G) * ((((r ⟨b, hb⟩ : ↥V) : G) * b⁻¹) * a⁻¹) := by group
            _ = ((r ⟨a, ha⟩ : ↥V) : G) * (a⁻¹ * (((r ⟨b, hb⟩ : ↥V) : G) * b⁻¹)) := by
                rw [hc1]
            _ = _ := by group
        rw [e]
        exact (Vt L t).mul_mem (hra r hr) (hrb r hr)
      one_mem' := ⟨V.one_mem, fun r _ => by
        have h1 : (⟨1, V.one_mem⟩ : ↥V) = 1 := rfl
        rw [h1, map_one]
        simp⟩
      inv_mem' := by
        rintro a ⟨ha, hra⟩
        refine ⟨V.inv_mem ha, fun r hr => ?_⟩
        have hm : (⟨a⁻¹, V.inv_mem ha⟩ : ↥V) = (⟨a, ha⟩ : ↥V)⁻¹ := rfl
        rw [hm, map_inv, Subgroup.coe_inv, inv_inv]
        have e : ((r ⟨a, ha⟩ : ↥V) : G)⁻¹ * a = (((r ⟨a, ha⟩ : ↥V) : G) * a⁻¹)⁻¹ := by
          rw [mul_inv_rev, inv_inv]
          exact hcV _ (V.inv_mem (r ⟨a, ha⟩).2) _ ha
        rw [e]
        exact (Vt L t).inv_mem (hra r hr) }
  have hWV : W ≤ V := fun g hg => hg.1
  have hVtW : Vt L t ≤ W := fun g hg => ⟨d.vt_le hg, fun r hr =>
    (Vt L t).mul_mem (hRVt r hr ⟨g, d.vt_le hg⟩ hg) ((Vt L t).inv_mem hg)⟩
  have hLtW : Lt L t ≤ Subgroup.normalizer (W : Set G) := by
    intro l hl
    refine Subgroup.mem_normalizer_fintype fun g hg => ?_
    obtain ⟨hgV, hgr⟩ := hg
    have hlN := d.lt_le_normalizer hl
    set c : MulAut ↥V := conjAct V ⟨l, hlN⟩ with hcdef
    have hcA : c ∈ autOn (Lt L t) V := ⟨⟨l, hlN⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have hlgV : l * g * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hlN g).mp hgV
    refine ⟨hlgV, fun r hr => ?_⟩
    have hr' : c⁻¹ * r * c ∈ R := (Subgroup.mem_normalizer_iff''.mp (hRn hcA) r).mp hr
    have hcg : c ⟨g, hgV⟩ = ⟨l * g * l⁻¹, hlgV⟩ := rfl
    have hrc : r ⟨l * g * l⁻¹, hlgV⟩ = c ((c⁻¹ * r * c) ⟨g, hgV⟩) := by
      rw [← hcg]
      simp only [MulAut.mul_apply, MulAut.apply_inv_self]
    rw [hrc]
    have hw := hgr _ hr'
    have hwV : ((c⁻¹ * r * c) ⟨g, hgV⟩ : G) * g⁻¹ ∈ V :=
      V.mul_mem ((c⁻¹ * r * c) ⟨g, hgV⟩).2 (V.inv_mem hgV)
    have hlc : l * (((c⁻¹ * r * c) ⟨g, hgV⟩ : G) * g⁻¹) * l⁻¹ =
        ((c⁻¹ * r * c) ⟨g, hgV⟩ : G) * g⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp (d.lt_le hl).2 _ hw
      rw [← this, mul_inv_cancel_right]
    have e : ((c ((c⁻¹ * r * c) ⟨g, hgV⟩) : ↥V) : G) * (l * g * l⁻¹)⁻¹ =
        l * (((c⁻¹ * r * c) ⟨g, hgV⟩ : G) * g⁻¹) * l⁻¹ := by
      show l * ((c⁻¹ * r * c) ⟨g, hgV⟩ : G) * l⁻¹ * (l * g * l⁻¹)⁻¹ = _
      group
    rw [e, hlc]
    exact hw
  obtain ⟨v, hvZ, hvfix⟩ := exists_fixed_coset hcV hR hRVt
    (by rw [d.card_quot]; norm_num)
  have hvW : (v : G) ∈ W := ⟨v.2, fun r hr => hvfix r hr⟩
  have hWeq : W = V := by
    rcases d.le_or_sup_eq hWV hLtW with hle | hsup
    · exact absurd (hle hvW) hvZ
    · rwa [sup_eq_left.mpr hVtW] at hsup
  intro r hr v
  have hv : (v : G) ∈ W := hWeq.symm.le v.2
  exact hv.2 r hr

theorem pCoreOf_autOn_eq_bot (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    pCoreOf 2 (autOn (Lt L t ⊔ T ⊓ Subgroup.centralizer ({t} : Set G)) V) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := Lt L t ⊔ T ⊓ Subgroup.centralizer ({t} : Set G) with hAdef
  have hLtN := d.lt_le_normalizer
  have hLtL : Lt L t ≤ L := d.lt_le.trans inf_le_left
  have hLtC : Lt L t ≤ Subgroup.centralizer ({t} : Set G) := (oTwoUpper_le _).trans inf_le_right
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := sup_le hLtN (inf_le_left.trans hTV)
  have hAM : A ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) :=
    sup_le (le_inf (hLtL.trans Subgroup.le_normalizer) hLtC)
      (le_inf (inf_le_left.trans d.hyp.hyp.normalizes) inf_le_right)
  have hALt : A ≤ Subgroup.normalizer (Lt L t : Set G) := by
    refine sup_le Subgroup.le_normalizer fun s hs => ?_
    exact normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨d.hyp.hyp.normalizes hs.1, Subgroup.le_normalizer hs.2⟩)
  set P := pCoreOf 2 (autOn A V) with hPdef
  have hPA : P ≤ autOn A V := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hAP : autOn A V ≤ Subgroup.normalizer (P : Set (MulAut ↥V)) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hLA : autOn (Lt L t) V ≤ autOn A V :=
    Subgroup.map_mono fun x hx => le_sup_left (a := Lt L t) hx
  have hAL : autOn A V ≤ Subgroup.normalizer (autOn (Lt L t) V : Set (MulAut ↥V)) :=
    autOn_le_normalizer_autOn hLtN hAN hALt
  have hpres : ∀ φ ∈ autOn A V, ∀ v : ↥V, (v : G) ∈ Vt L t → ((φ v : ↥V) : G) ∈ Vt L t := by
    intro φ hφ v hv
    obtain ⟨a, rfl⟩ := (A4.mem_autOn_iff hAN).1 hφ
    rw [A4.actionOn_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_Vt (hAM a.2).1 (hAM a.2).2) v).mp hv
  have hR : P ⊓ autOn (Lt L t) V = ⊥ := by
    have hRn : autOn (Lt L t) V ≤
        Subgroup.normalizer ((P ⊓ autOn (Lt L t) V : Subgroup (MulAut ↥V)) : Set (MulAut ↥V)) :=
      fun c hc => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hAP (hLA hc), Subgroup.le_normalizer hc⟩
    have htriv := d.trivial_mod_Vt (hP2.to_le inf_le_left) (fun r hr => hpres r (hPA hr.1)) hRn
    refine eq_bot_iff.mpr fun r hr => ?_
    obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLtN).1 hr.2
    obtain ⟨F, _, _, -, hNS⟩ := d.nat
    obtain ⟨-, α, -, hαk, β, hβs, hβk, hβ⟩ := hNS
    set lB : ↥(L ⊓ Subgroup.centralizer (Vt L t : Set G)) := ⟨l, d.lt_le l.2⟩ with hlB
    have hfix : ∀ w : Fin 2 → F,
        ((α lB : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w = w := by
      intro w
      obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd w)
      have hlv : (l : G) * v * (l : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hLtN l.2) v).mp v.2
      have h1 := hβ lB v ⟨_, hlv⟩ rfl
      have h2 : β ⟨_, hlv⟩ = β v := by
        have hk : (⟨_, hlv⟩ * v⁻¹ : ↥V) ∈ β.ker := by
          rw [hβk, Subgroup.mem_subgroupOf]
          exact htriv _ hr v
        rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
      rw [h2, hv] at h1
      simpa only [toAdd_ofAdd] using h1.symm
    have hα1 : α lB = 1 := by
      have hM : ((α lB : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
        ext i j
        have := congrFun (hfix (Pi.single j 1)) i
        simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply] using this
      exact Subtype.ext (Units.ext hM)
    have hlk : lB ∈ α.ker := hα1
    rw [hαk, Subgroup.mem_subgroupOf] at hlk
    exact Subgroup.mem_bot.mpr ((A4.actionOn_eq_one_iff hLtN l).mpr hlk)
  have hcomm : ∀ p ∈ P, ∀ c ∈ autOn (Lt L t) V, p * c = c * p := by
    intro p hp c hc
    have h1 : p * c * p⁻¹ * c⁻¹ ∈ P := by
      have h := (Subgroup.mem_normalizer_iff.mp (hAP (hLA hc)) _).mp (P.inv_mem hp)
      simpa only [mul_assoc] using P.mul_mem hp h
    have h2 : p * c * p⁻¹ * c⁻¹ ∈ autOn (Lt L t) V :=
      (autOn (Lt L t) V).mul_mem ((Subgroup.mem_normalizer_iff.mp (hAL (hPA hp)) c).mp hc)
        ((autOn (Lt L t) V).inv_mem hc)
    have h3 : p * c * p⁻¹ * c⁻¹ = 1 := by
      have h : p * c * p⁻¹ * c⁻¹ ∈ P ⊓ autOn (Lt L t) V := ⟨h1, h2⟩
      rw [hR] at h
      exact h
    calc p * c = p * c * p⁻¹ * c⁻¹ * (c * p) := by group
      _ = c * p := by rw [h3, one_mul]
  have htP := d.trivial_mod_Vt hP2 (fun r hr => hpres r (hPA hr)) (hLA.trans hAP)
  refine eq_bot_iff.mpr fun p hp => Subgroup.mem_bot.mpr ?_
  have hK : ⁅V, Lt L t⁆ ≤ (MonoidHom.eqLocus (p : MulAut ↥V).toMonoidHom (MonoidHom.id ↥V)).map
      V.subtype := by
    refine Subgroup.commutator_le.mpr fun g hg l hl => ?_
    have hlN := hLtN hl
    set c : MulAut ↥V := conjAct V ⟨l, hlN⟩ with hcdef
    have hcA : c ∈ autOn (Lt L t) V := ⟨⟨l, hlN⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have hgi : l * g⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hlN _).mp (V.inv_mem hg)
    have hxV : g * l * g⁻¹ * l⁻¹ ∈ V := by
      have := V.mul_mem hg hgi
      simpa only [mul_assoc] using this
    refine ⟨⟨_, hxV⟩, ?_, by simp [commutatorElement_def]⟩
    have hxe : (⟨_, hxV⟩ : ↥V) = ⟨g, hg⟩ * c ⟨g⁻¹, V.inv_mem hg⟩ :=
      Subtype.ext (by show g * l * g⁻¹ * l⁻¹ = g * (l * g⁻¹ * l⁻¹); group)
    show p ⟨_, hxV⟩ = ⟨_, hxV⟩
    have hpc : p (c ⟨g⁻¹, V.inv_mem hg⟩) = c (p ⟨g⁻¹, V.inv_mem hg⟩) := by
      have := congrArg (fun φ : MulAut ↥V => φ ⟨g⁻¹, V.inv_mem hg⟩) (hcomm p hp c hcA)
      simpa only [MulAut.mul_apply] using this
    have hinv : p ⟨g⁻¹, V.inv_mem hg⟩ = (p ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    refine Subtype.ext ?_
    rw [hxe, map_mul, hpc, hinv]
    set y : G := ((p ⟨g, hg⟩ : ↥V) : G) with hydef
    show y * (l * y⁻¹ * l⁻¹) = g * (l * g⁻¹ * l⁻¹)
    have hδ : y * g⁻¹ ∈ Vt L t := htP p hp ⟨g, hg⟩
    have hδl : y * g⁻¹ * l = l * (y * g⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (d.lt_le hl).2 _ hδ
    have hδx := d.comm _ (d.vt_le hδ) _ hxV
    have e1 : (y * g⁻¹)⁻¹ * l⁻¹ = l⁻¹ * (y * g⁻¹)⁻¹ := by
      simpa only [mul_inv_rev] using (congrArg (·⁻¹) hδl).symm
    calc y * (l * y⁻¹ * l⁻¹) = (y * g⁻¹) * (g * l * g⁻¹ * ((y * g⁻¹)⁻¹ * l⁻¹)) := by group
      _ = (y * g⁻¹) * (g * l * g⁻¹ * l⁻¹) * (y * g⁻¹)⁻¹ := by rw [e1]; group
      _ = g * (l * g⁻¹ * l⁻¹) := by rw [hδx]; group
  ext v
  have hvK : (v : G) ∈ ⁅V, Lt L t⁆ := by
    rw [← d.comm_eq]
    exact v.2
  obtain ⟨x, hx, hxv⟩ := hK hvK
  have hxv' : x = v := Subtype.ext hxv
  subst hxv'
  exact congrArg Subtype.val hx

end D127

end CFSG.Quasithin.H13.S127.L5
