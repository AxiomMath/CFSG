module

public import CFSG.Quasithin.H13.KGFactF9187Z
public import CFSG.Quasithin.H13.KGFactHatM22FF
public import CFSG.Quasithin.H13.L32ACSk5
public import CFSG.Quasithin.H13.L32AC47c
public import CFSG.Quasithin.H13.L32AC36c
public import CFSG.Quasithin.H13.L32ASk4
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.KGFFZ

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin
open scoped Pointwise commutatorElement

section Norm

variable {W : Type*} [CommGroup W]

theorem norm_eq_one_of_mem_closure (σ : W ≃* W) (hσ3 : ∀ w, σ (σ (σ w)) = w)
    (hgen : ∀ w : W, w ∈ Subgroup.closure {u | ∃ v, u = σ v * v⁻¹}) :
    ∀ w : W, w * σ w * σ (σ w) = 1 := by
  intro w
  induction hgen w using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨v, rfl⟩ := hu
    simp only [map_mul, map_inv, hσ3]
    calc σ v * v⁻¹ * (σ (σ v) * (σ v)⁻¹) * (v * (σ (σ v))⁻¹)
        = (σ v * (σ v)⁻¹) * (v * v⁻¹) * (σ (σ v) * (σ (σ v))⁻¹) := by ac_rfl
      _ = 1 := by simp
  | one => simp
  | mul a b _ _ ha hb =>
    simp only [map_mul]
    calc a * b * (σ a * σ b) * (σ (σ a) * σ (σ b))
        = (a * σ a * σ (σ a)) * (b * σ b * σ (σ b)) := by ac_rfl
      _ = 1 := by rw [ha, hb, one_mul]
  | inv a _ ha =>
    simp only [map_inv]
    calc a⁻¹ * (σ a)⁻¹ * (σ (σ a))⁻¹ = (a * σ a * σ (σ a))⁻¹ := by
          simp only [mul_inv_rev]
          ac_rfl
      _ = 1 := by rw [ha, inv_one]

theorem le_of_trivial_section (hsq : ∀ a : W, a * a = 1) (σ : W ≃* W)
    (hn : ∀ w : W, w * σ w * σ (σ w) = 1) {E F : Subgroup W} (hF : ∀ f ∈ F, σ f ∈ F)
    (htriv : ∀ e ∈ E, σ e * e⁻¹ ∈ F) : E ≤ F := by
  intro e he
  set f := σ e * e⁻¹ with hfdef
  have hf : f ∈ F := htriv e he
  have h1 : σ e = f * e := by rw [hfdef, inv_mul_cancel_right]
  have h2 : σ (σ e) = σ f * (f * e) := by rw [h1, map_mul, h1]
  have hne := hn e
  rw [h2, h1] at hne
  have key : e * (f * e) * (σ f * (f * e)) = (e * e) * (f * f) * e * σ f := by ac_rfl
  rw [key, hsq, hsq, one_mul, one_mul] at hne
  have : e = (σ f)⁻¹ := eq_inv_of_mul_eq_one_left hne
  rw [this]
  exact F.inv_mem (hF f hf)

end Norm

section Module

variable {G : Type} [Group G] {V₁ IH H : Subgroup G}

attribute [local instance] commGroupOfFact

theorem zpow_mul_inv_mem_closure {W : Type*} [CommGroup W] (σ : W ≃* W) (k : ℤ) (v : W) :
    (σ ^ k) v * v⁻¹ ∈ Subgroup.closure {u | ∃ v, u = σ v * v⁻¹} := by
  induction k using Int.induction_on generalizing v with
  | zero => simp
  | succ k ih =>
    have e : (σ ^ ((k : ℤ) + 1)) v * v⁻¹ =
        (σ ((σ ^ (k : ℤ)) v) * ((σ ^ (k : ℤ)) v)⁻¹) * ((σ ^ (k : ℤ)) v * v⁻¹) := by
      rw [add_comm (k : ℤ) 1, zpow_one_add, MulAut.mul_apply]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨_, rfl⟩) (ih v)
  | pred k ih =>
    have e : (σ ^ (-(k : ℤ) - 1)) v * v⁻¹ =
        (σ ((σ ^ (-(k : ℤ) - 1)) v) * ((σ ^ (-(k : ℤ) - 1)) v)⁻¹)⁻¹ *
          ((σ ^ (-(k : ℤ))) v * v⁻¹) := by
      have h1 : σ ((σ ^ (-(k : ℤ) - 1)) v) = (σ ^ (-(k : ℤ))) v := by
        rw [← MulAut.mul_apply, ← zpow_one_add]
        congr 2
        ring
      rw [h1]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨_, rfl⟩)) (ih v)

variable [Fact (IsElemAbelian 2 (tildeOf V₁ IH))]

theorem norm_eq_one_of_comm_sup (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (hIH : H ≤ Subgroup.normalizer (IH : Set G))
    (hV₁IH : V₁ ≤ IH) {y : G} (hy : y ∈ H) (hy3 : y ^ 3 = 1)
    (hU : ⁅IH, Subgroup.zpowers y⁆ ⊔ V₁ = IH) :
    ∀ w : ↥(tildeOf V₁ IH), w * actH hV₁ hIH ⟨y, hy⟩ w *
      actH hV₁ hIH ⟨y, hy⟩ (actH hV₁ hIH ⟨y, hy⟩ w) = 1 := by
  set σ := actH hV₁ hIH ⟨y, hy⟩ with hσ
  have hσ3 : ∀ w, σ (σ (σ w)) = w := by
    intro w
    have h3 : σ ^ 3 = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨y, hy⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    have := congrArg (fun φ : MulAut ↥(tildeOf V₁ IH) => φ w) h3
    simpa [pow_succ, MulAut.mul_apply] using this
  refine norm_eq_one_of_mem_closure σ hσ3 fun w => ?_
  set P : Subgroup G :=
    ((Subgroup.closure {u | ∃ v, u = σ v * v⁻¹}).comap (tildeHom hIHN)).map IH.subtype with hP
  have hmemP : ∀ u (hu : u ∈ IH), modMk hIHN u hu ∈ Subgroup.closure {u | ∃ v, u = σ v * v⁻¹} →
      u ∈ P := fun u hu h => ⟨⟨u, hu⟩, h, rfl⟩
  have hV₁P : V₁ ≤ P := by
    intro v hv
    refine hmemP v (hV₁IH hv) ?_
    have : modMk hIHN v (hV₁IH hv) = 1 := by
      apply Subtype.ext
      show secMk _ _ ⟨v, hIHN (hV₁IH hv)⟩ = 1
      exact secMk_eq_one_iff.mpr hv
    rw [this]
    exact Subgroup.one_mem _
  have hcP : ⁅IH, Subgroup.zpowers y⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro u hu z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hyk : y ^ k ∈ H := H.zpow_mem hy k
    have hc : y ^ k * u⁻¹ * (y ^ k)⁻¹ ∈ IH :=
      (Subgroup.mem_normalizer_iff.mp (hIH hyk) u⁻¹).mp (IH.inv_mem hu)
    have hcu : ⁅u, y ^ k⁆ ∈ IH := by
      rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc (y ^ k)]
      exact IH.mul_mem hu hc
    refine hmemP _ hcu ?_
    have e1 : modMk hIHN ⁅u, y ^ k⁆ hcu =
        modMk hIHN u hu * actH hV₁ hIH ⟨y ^ k, hyk⟩ (modMk hIHN u⁻¹ (IH.inv_mem hu)) := by
      rw [actH_modMk hV₁ hIHN hIH ⟨y ^ k, hyk⟩ (IH.inv_mem hu), ← modMk_mul]
      congr 1
      rw [commutatorElement_def]
      group
    have e2 : actH hV₁ hIH ⟨y ^ k, hyk⟩ = σ ^ k := by
      rw [hσ, ← map_zpow]
      rfl
    rw [e1, e2, modMk_inv hIHN hu, map_inv]
    have := zpow_mul_inv_mem_closure σ k (modMk hIHN u hu)
    have e3 : modMk hIHN u hu * ((σ ^ k) (modMk hIHN u hu))⁻¹ =
        ((σ ^ k) (modMk hIHN u hu) * (modMk hIHN u hu)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
    rw [e3]
    exact Subgroup.inv_mem _ this
  have hUP : IH ≤ P := by
    rw [← hU]
    exact sup_le hcP hV₁P
  obtain ⟨a, ha, hwa⟩ := exists_mk_of_mem_tilde w
  have hw : w = modMk hIHN (a : G) ha := Subtype.ext hwa.symm
  obtain ⟨⟨u, huIH⟩, hu, hua⟩ := hUP ha
  have hu' : (u : G) = a := hua
  rw [hw]
  have : modMk hIHN (a : G) ha = tildeHom hIHN ⟨u, huIH⟩ := by
    apply Subtype.ext
    show secMk _ _ ⟨(a : G), hIHN ha⟩ = secMk _ _ ⟨u, hIHN huIH⟩
    congr 2
    exact hu'.symm
  rw [this]
  exact hu

theorem le_of_trivial_mod (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (hIH : H ≤ Subgroup.normalizer (IH : Set G))
    (hV₁IH : V₁ ≤ IH) {y : G} (hy : y ∈ H) (hy3 : y ^ 3 = 1)
    (hU : ⁅IH, Subgroup.zpowers y⁆ ⊔ V₁ = IH) {E F : Subgroup G} (hV₁F : V₁ ≤ F) (hFE : F ≤ E)
    (hEIH : E ≤ IH) (hyF : y ∈ Subgroup.normalizer (F : Set G))
    (htriv : ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ F) : E ≤ F := by
  have hn := norm_eq_one_of_comm_sup hV₁ hIHN hIH hV₁IH hy hy3 hU
  set σ := actH hV₁ hIH ⟨y, hy⟩ with hσ
  have hsq : ∀ a : ↥(tildeOf V₁ IH), a * a = 1 := fun a => by
    rw [← sq]
    exact Subtype.ext (by simpa using (Fact.out : IsElemAbelian 2 (tildeOf V₁ IH)).2 _ a.2)
  have hV₁E : V₁ ≤ E := hV₁F.trans hFE
  have hle := le_of_trivial_section hsq σ hn (E := subM V₁ IH E) (F := subM V₁ IH F)
    (fun f hf => by
      obtain ⟨a, ha, hfa⟩ := exists_mk_of_mem_tilde f
      have hf' : f = modMk hIHN (a : G) ha := Subtype.ext hfa.symm
      rw [hf'] at hf ⊢
      rw [hσ, actH_modMk hV₁ hIHN hIH ⟨y, hy⟩ ha, modMk_mem_subM_iff hIHN hV₁F]
      exact (Subgroup.mem_normalizer_iff.mp hyF _).mp
        ((modMk_mem_subM_iff hIHN hV₁F ha).mp hf))
    (fun e he => by
      obtain ⟨a, ha, hea⟩ := exists_mk_of_mem_tilde e
      have he' : e = modMk hIHN (a : G) ha := Subtype.ext hea.symm
      rw [he'] at he ⊢
      have haE : (a : G) ∈ E := (modMk_mem_subM_iff hIHN hV₁E ha).mp he
      rw [hσ, actH_modMk hV₁ hIHN hIH ⟨y, hy⟩ ha, ← modMk_inv, ← modMk_mul,
        modMk_mem_subM_iff hIHN hV₁F]
      exact htriv _ haE)
  intro e he
  have h1 : modMk hIHN e (hEIH he) ∈ subM V₁ IH E := (modMk_mem_subM_iff hIHN hV₁E _).mpr he
  exact (modMk_mem_subM_iff hIHN hV₁F _).mp (hle h1)


theorem mem_of_comm_mem (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (hIH : H ≤ Subgroup.normalizer (IH : Set G))
    (hV₁IH : V₁ ≤ IH) {y : G} (hy : y ∈ H) (hy3 : y ^ 3 = 1)
    (hU : ⁅IH, Subgroup.zpowers y⁆ ⊔ V₁ = IH) {a : G} (ha : a ∈ IH)
    (hya : y * a * y⁻¹ * a⁻¹ ∈ V₁) : a ∈ V₁ := by
  have hV₁N : y ∈ Subgroup.normalizer (V₁ : Set G) := hV₁ hy
  have hle := le_of_trivial_mod hV₁ hIHN hIH hV₁IH hy hy3 hU (E := Subgroup.zpowers a ⊔ V₁)
    (F := V₁) le_rfl le_sup_right (sup_le (Subgroup.zpowers_le.mpr ha) hV₁IH) hV₁N ?_
  · exact hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  ·
    intro e he
    let D : Subgroup G :=
      { carrier := {e | e ∈ Subgroup.normalizer (V₁ : Set G) ∧ y * e * y⁻¹ * e⁻¹ ∈ V₁}
        mul_mem' := by
          rintro e f ⟨heN, he⟩ ⟨hfN, hf⟩
          refine ⟨Subgroup.mul_mem _ heN hfN, ?_⟩
          have h1 : y * (e * f) * y⁻¹ * (e * f)⁻¹ =
              (y * e * y⁻¹ * e⁻¹) * (e * (y * f * y⁻¹ * f⁻¹) * e⁻¹) := by group
          rw [h1]
          exact V₁.mul_mem he ((Subgroup.mem_normalizer_iff.mp heN _).mp hf)
        one_mem' := ⟨Subgroup.one_mem _, by simp⟩
        inv_mem' := by
          rintro e ⟨heN, he⟩
          refine ⟨Subgroup.inv_mem _ heN, ?_⟩
          have h1 : y * e⁻¹ * y⁻¹ * e⁻¹⁻¹ =
              e⁻¹ * (y * e * y⁻¹ * e⁻¹)⁻¹ * e := by group
          rw [h1]
          exact (Subgroup.mem_normalizer_iff''.mp heN _).mp (V₁.inv_mem he) }
    have hDa : Subgroup.zpowers a ⊔ V₁ ≤ D := by
      refine sup_le (Subgroup.zpowers_le.mpr ⟨hIHN ha, hya⟩) fun v hv =>
        ⟨Subgroup.le_normalizer hv, ?_⟩
      have h1 : y * v * y⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hV₁N v).mp hv
      exact V₁.mul_mem h1 (V₁.inv_mem hv)
    exact (hDa he).2

end Module


section Hat

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.L32A.C CFSG.Blueprint

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem comm_of_commutator_eq_one {M : Type*} [Group M] {a b : M} (h : a * b * a⁻¹ * b⁻¹ = 1) :
    b * a = a * b :=
  calc b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by group
    _ = a * b := by rw [h, inv_one, one_mul]

omit [Finite G] in
theorem mem_pCore_iff' {x : ↥H} : x ∈ CFSG.pCore 2 ↥H ↔ (x : G) ∈ pCoreOf 2 H :=
  (CFSG.mem_openPCoreOf_iff x).symm

theorem hat_center (h28 : Lemma14_7_28) (h5 : Lemma14_7_5) (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H)
    (hhat : IsHat (cStar K) (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    (modO2Image H (l1 T L V)).Normal ∧
    (∀ x ∈ K, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → x ^ 3 ∈ pCoreOf 2 H) ∧
    (∀ x ∈ K, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → x ∉ pCoreOf 2 H →
      ∀ l ∈ l1 T L V, ∃ n : ℤ, (x ^ n)⁻¹ * l ∈ pCoreOf 2 H) ∧
    ∃ x ∈ K, (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) ∧ x ∉ pCoreOf 2 H := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  set Kb := modO2Image H K with hKb
  have hcard : Nat.card (Subgroup.center ↥Kb) = 3 := by
    rw [← card_center_eq_of_mulEquiv ((cStarEquiv K).trans e)]
    exact hhat.2.1
  set Z := Subgroup.center ↥Kb with hZ
  set Zb := Z.map Kb.subtype with hZbdef
  have hKbs : Kb.IsSubnormal := A3.subnormal_top_iff.mp (modO2Image_mem_cComp hK).2.2.1
  have hZn : ((Z.map Kb.subtype).subgroupOf Kb).Normal := by
    rw [map_subtype_subgroupOf']
    infer_instance
  have hZs : Zb.IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (Subgroup.map_subtype_le Z) hKbs hZn
  have hZc : Nat.card Zb = 3 := by
    rw [hZbdef, Subgroup.card_map_of_injective Kb.subtype_injective, hcard]
  have hle : Zb ≤ CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) :=
    le_oddCore_of_isSubnormal hZs (by rw [hZc]; exact ⟨1, rfl⟩)
  have hO : CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = modO2Image H (l1 T L V) := by
    rcases h28 G T L V H S with h0 | h1
    · rw [h0, le_bot_iff] at hle
      rw [hle, Subgroup.card_bot] at hZc
      omega
    · exact h1
  have hnorm : (modO2Image H (l1 T L V)).Normal := by
    rw [← hO]
    infer_instance
  obtain ⟨-, -, hL3, -⟩ := h5 G T L V H S hnorm
  have hZL : Zb = modO2Image H (l1 T L V) :=
    Subgroup.eq_of_le_of_card_ge (hle.trans hO.le) (hL3.trans hZc.symm).le
  have hcen : ∀ x (hx : x ∈ K), (∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
      (QuotientGroup.mk (⟨x, hKH hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Zb := by
    intro x hx hxc
    have hmem : (QuotientGroup.mk (⟨x, hKH hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Kb :=
      ⟨⟨x, hKH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    refine ⟨⟨_, hmem⟩, Subgroup.mem_center_iff.mpr fun k => ?_, rfl⟩
    obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.mp k.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hkk]
    have hk'K : (k' : G) ∈ K := Subgroup.mem_subgroupOf.mp hk'
    have hc : (⟨x, hKH hx⟩ : ↥H) * k' * (⟨x, hKH hx⟩ : ↥H)⁻¹ * k'⁻¹ ∈ CFSG.pCore 2 ↥H :=
      mem_pCore_iff'.mpr (hxc _ hk'K)
    have h1 := (QuotientGroup.eq_one_iff _).mpr hc
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    exact comm_of_commutator_eq_one h1
  refine ⟨hnorm, fun x hx hxc => ?_, fun x hx hxc hxQ l hl => ?_, ?_⟩
  · have h1 := hcen x hx hxc
    have h3 : (QuotientGroup.mk (⟨x, hKH hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥Zb) (x := ⟨_, h1⟩)
      rw [hZc] at this
      exact congrArg Subtype.val this
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h3
    exact mem_pCore_iff'.mp h3
  · set xb := (QuotientGroup.mk (⟨x, hKH hx⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) with hxb
    have h1 := hcen x hx hxc
    have hxb1 : xb ≠ 1 := by
      intro h
      rw [hxb, QuotientGroup.eq_one_iff] at h
      exact hxQ (mem_pCore_iff'.mp h)
    have hzle : Subgroup.zpowers xb ≤ Zb := Subgroup.zpowers_le.mpr h1
    have hord : orderOf xb ∣ 3 := by
      rw [← hZc]
      exact Subgroup.orderOf_dvd_natCard Zb h1
    have hord3 : orderOf xb = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hxb1
      · exact h
    have hzeq : Subgroup.zpowers xb = modO2Image H (l1 T L V) := by
      rw [← hZL]
      exact Subgroup.eq_of_le_of_card_ge hzle (le_of_eq (by rw [Nat.card_zpowers, hord3, hZc]))
    have hlH : l ∈ H := le_sup_left.trans S.hz.1.1 hl
    have hlb : (QuotientGroup.mk (⟨l, hlH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
        Subgroup.zpowers xb := by
      rw [hzeq]
      exact ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hlb
    refine ⟨n, ?_⟩
    rw [hxb, ← QuotientGroup.mk_zpow] at hn
    exact mem_pCore_iff'.mp (QuotientGroup.eq.mp hn)
  ·
    have : Nontrivial ↥Zb := Finite.one_lt_card_iff_nontrivial.mp (by rw [hZc]; norm_num)
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥Zb)
    obtain ⟨w, hwZ, hwz⟩ := Subgroup.mem_map.mp z.2
    obtain ⟨h', hh'K, hh'w⟩ := Subgroup.mem_map.mp w.2
    refine ⟨(h' : G), Subgroup.mem_subgroupOf.mp hh'K, fun k hk => ?_, fun hQ => hz1 ?_⟩
    · have hkb : (QuotientGroup.mk (⟨k, hKH hk⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Kb :=
        ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      have hc : (QuotientGroup.mk (⟨k, hKH hk⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) *
          (w : ↥H ⧸ CFSG.pCore 2 ↥H) =
          (w : ↥H ⧸ CFSG.pCore 2 ↥H) * QuotientGroup.mk ⟨k, hKH hk⟩ :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hwZ (⟨_, hkb⟩ : ↥Kb))
      have hw' : (w : ↥H ⧸ CFSG.pCore 2 ↥H) = QuotientGroup.mk h' := hh'w.symm
      have hmem : h' * ⟨k, hKH hk⟩ * h'⁻¹ * (⟨k, hKH hk⟩ : ↥H)⁻¹ ∈ CFSG.pCore 2 ↥H := by
        rw [← QuotientGroup.eq_one_iff]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [← hw', ← hc]
        group
      exact mem_pCore_iff'.mp hmem
    · apply Subtype.ext
      rw [← hwz]
      show (w : ↥H ⧸ CFSG.pCore 2 ↥H) = 1
      rw [← hh'w]
      exact (QuotientGroup.eq_one_iff _).mpr (mem_pCore_iff'.mpr hQ)

theorem exists_pow_three {H : Subgroup G} {x : G} (hx3 : x ^ 3 ∈ pCoreOf 2 H)
    (hxQ : x ∉ pCoreOf 2 H) : ∃ m : ℕ, (x ^ m) ^ 3 = 1 ∧ x ^ m ∉ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 H) ⟨_, hx3⟩
  have ha' : (x ^ 3) ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have h4 : (4 : ℕ) ^ a = 2 ^ a * 2 ^ a := by rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
  refine ⟨4 ^ a, ?_, fun hm => hxQ ?_⟩
  · rw [← pow_mul, h4, show 2 ^ a * 2 ^ a * 3 = 3 * 2 ^ a * 2 ^ a by ring, pow_mul, pow_mul, ha',
      one_pow]
  · obtain ⟨c, hc⟩ : ∃ c, 4 ^ a = 3 * c + 1 := by
      refine ⟨(4 ^ a - 1) / 3, ?_⟩
      have h1 : 4 ^ a % 3 = 1 := by simp [Nat.pow_mod]
      have h2 : 1 ≤ 4 ^ a := Nat.one_le_pow _ _ (by norm_num)
      omega
    have e : x ^ (4 ^ a) * ((x ^ 3) ^ c)⁻¹ = x := by
      rw [hc, ← pow_mul, pow_succ', mul_inv_cancel_right]
    have := (pCoreOf 2 H).mul_mem hm ((pCoreOf 2 H).inv_mem ((pCoreOf 2 H).pow_mem hx3 c))
    rwa [e] at this

omit [Finite G] in
theorem commutator_zpowers_sup_eq {U V₁ L₁ Q : Subgroup G} {y : G} (hyH : y ∈ H)
    (hUn : H ≤ Subgroup.normalizer (U : Set G)) (hV₁n : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hV₁U : V₁ ≤ U) (hUL : ⁅U, L₁⁆ ⊔ V₁ = U)
    (hQ : ∀ u ∈ U, ∀ q ∈ Q, u * q * u⁻¹ * q⁻¹ ∈ V₁)
    (hL : ∀ l ∈ L₁, ∃ n : ℤ, (y ^ n)⁻¹ * l ∈ Q) :
    ⁅U, Subgroup.zpowers y⁆ ⊔ V₁ = U := by
  apply le_antisymm
  · refine sup_le ?_ hV₁U
    rw [Subgroup.commutator_le]
    intro u hu z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hyk : y ^ k ∈ H := H.zpow_mem hyH k
    have hc : y ^ k * u⁻¹ * (y ^ k)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hUn hyk) u⁻¹).mp (U.inv_mem hu)
    rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc (y ^ k)]
    exact U.mul_mem hu hc
  · refine hUL.symm.le.trans (sup_le ?_ le_sup_right)
    rw [Subgroup.commutator_le]
    intro u hu l hl
    obtain ⟨n, hn⟩ := hL l hl
    have hyn : y ^ n ∈ H := H.zpow_mem hyH n
    have e : ⁅u, l⁆ = ⁅u, y ^ n⁆ *
        (y ^ n * (u * ((y ^ n)⁻¹ * l) * u⁻¹ * ((y ^ n)⁻¹ * l)⁻¹) * (y ^ n)⁻¹) := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hu
        (Subgroup.zpow_mem_zpowers y n)))
      (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hV₁n hyn) _).mp (hQ u hu _ hn)))

omit [Finite G] in
theorem mem_stabSub_of_eq_orbSup' {W : Type} [CommGroup W] {T : Subgroup (MulAut W)}
    {U : Subgroup W} (h : U = orbSup T U) {t : MulAut W} (ht : t ∈ T) : t ∈ stabSub U := by
  have hmap : ∀ s ∈ T, ∀ u ∈ U, s u ∈ U := by
    intro s hs u hu
    rw [h]
    exact (le_iSup₂ (f := fun s (_ : s ∈ T) => U.map s.toMonoidHom) s hs) ⟨u, hu, rfl⟩
  intro u
  refine ⟨fun hu => ?_, hmap t ht u⟩
  have := hmap t⁻¹ (T.inv_mem ht) _ hu
  simpa using this

omit [Finite G] in
theorem card_cStar_hat {K : Subgroup G}
    (hhat : IsHat (cStar K) (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    Nat.card (cStar K) = 1330560 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hhat
  have e' : cStar K ⧸ Subgroup.center (cStar K) ≃* ↥NativeSporadic.M22 := e
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (cStar K)),
    Nat.card_congr e'.toEquiv, CFSG.Sporadic.Mathieu.card_M22, hZ]

theorem card_autIH_eq {V₁ Vp K I : Subgroup G} (hF : HypF918 T V L V₁ Vp H K)
    (hH : H = conjClosure K T ⊔ T) (hZ : SectionFaithful T V₁ Vp H K) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) :
    Nat.card ↥(autIH V₁ I H K) = Nat.card (cStar K) := by
  have := factElem hF hIU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIHN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    hF.K₀T_le_H.trans (le_normalizer_conjClosure I H)
  have hnt' : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ conjClosure I H, k * e * k⁻¹ * e⁻¹ ∈ V₁ :=
    fun hall => hnt fun k hk i hi => hall k hk i (le_conjClosure I H hi)
  have hQV₁ : ∀ x ∈ pCoreOf 2 H, ∀ e ∈ conjClosure I H, x * e * x⁻¹ * e⁻¹ ∈ V₁ := by
    intro x hx e he
    have := V₁.inv_mem (hF.toHypF98.toHypF91.commutator_conjClosure_le e (hIHU he) x hx)
    have e' : (e * x * e⁻¹ * x⁻¹)⁻¹ = x * e * x⁻¹ * e⁻¹ := by group
    rwa [e'] at this
  have hker := ker_le_pCoreOf' hF hH hF.K₀T_le_normalizer_V₁ hIHN hnt' hQV₁
    (hZ V₁ (conjClosure I H) le_rfl (hV₁I.trans (le_conjClosure I H)) hIHU
      hF.K₀T_le_normalizer_V₁ hIHN hnt')
  have hKQ : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun k hk => ?_)
      ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) g)
      (Subgroup.mem_normalizer_iff.mp (hQn (hKH hk)) g)
  have hkereq : (toAutI hF I).ker = CFSG.pCore 2 ↥K := by
    refine le_antisymm (fun x hx => ?_) (pCore_le_ker_toAutI hF hIU)
    rw [MonoidHom.mem_ker, toAutI_eq_one_iff] at hx
    have hxQ : (x : G) ∈ pCoreOf 2 H :=
      hker x (hH.le (hKH x.2)) (hF.commutator_mem_of_actH_eq_one hIU hx)
    exact (coe_mem_pCoreOf_iff_mem_pCore x).mp (hKQ ⟨x.2, hxQ⟩)
  have e := QuotientGroup.quotientKerEquivOfSurjective (toAutI hF I) (toAutI_surjective hF I)
  rw [← Nat.card_congr e.toEquiv,
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hkereq).toEquiv,
    ← Nat.card_congr (cStarEquiv K).toEquiv]

end Hat

section Main

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.L32A CFSG.Quasithin.H13.L32A.C CFSG.Blueprint

attribute [local instance] commGroupOfFact

theorem lemma14_7_36_hatIrr_of (h28 : Lemma14_7_28)
    (h5 : Lemma14_7_5) (h30 : Lemma14_7_30) (h32 : Lemma14_7_32) (h56 : AsB56) (hD310 : D310)
    (hD391 : D391) (hI4 : Insp4) (hFine : F918Fine4) : Lemma14_7_36_HatIrr := by
  intro G _ _ T L V H S K hK hHeq hhat J hV₁J hJU hKJ
  obtain ⟨hq, hTK, -, hF⟩ := reduce_KL1T h30 h32 S hK
  rw [← hHeq] at hF
  have hK₀ : conjClosure K T = K := conjClosure_T_eq_self hTK
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := hF.T_le_H
  have hQT : pCoreOf 2 H ≤ T := isSylowTwoOf_pCoreOf_le hF.sylow_H
  have hQn : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hSQ := sqtkGroup_of_setting S
  obtain ⟨hnorm, hx3, hgen, x₀, hx₀K, hx₀c, hx₀Q⟩ := hat_center h28 h5 S hK hhat
  obtain ⟨-, -, -, -, -, -, h7⟩ := h5 G T L V H S hnorm
  have hHKT : H = K ⊔ T := by
    refine le_antisymm ?_ (sup_le hKH hTH)
    rw [hHeq]
    refine sup_le le_sup_left (sup_le (fun l hl => ?_) le_sup_right)
    obtain ⟨n, hn⟩ := hgen x₀ hx₀K hx₀c hx₀Q l hl
    rw [← mul_inv_cancel_left (x₀ ^ n) l]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.zpow_mem hx₀K n))
      (Subgroup.mem_sup_right (hQT hn))
  have hHeq' : H = conjClosure K T ⊔ T := by rw [hK₀]; exact hHKT
  have hKn : (K.subgroupOf H).Normal := by
    have h0 := hF.K₀_normal
    rw [hK₀] at h0
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr h0
  have hFU := factElem hF (le_conjClosure V H)
  have hV₁H : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_le_normalizer_V₁
  have hUN : conjClosure V H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure V H)
  have hUH : H ≤ Subgroup.normalizer (conjClosure V H : Set G) := le_normalizer_conjClosure V H
  have hV₁U : fsuV1 T V ≤ conjClosure V H :=
    hF.toHypF98.toHypF91.V₁_le_Vp.trans (le_conjClosure V H)
  have hUQ : ∀ u ∈ conjClosure V H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ fsuV1 T V :=
    hF.toHypF98.toHypF91.commutator_conjClosure_le
  have hkey : ∀ y ∈ K, (∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 H) → y ∉ pCoreOf 2 H →
      ⁅conjClosure V H, Subgroup.zpowers y⁆ ⊔ fsuV1 T V = conjClosure V H :=
    fun y hyK hyc hyQ =>
      commutator_zpowers_sup_eq (hKH hyK) hUH hV₁H hV₁U h7 hUQ (hgen y hyK hyc hyQ)
  obtain ⟨m, hm3, hmQ⟩ := exists_pow_three (hx3 x₀ hx₀K hx₀c) hx₀Q
  have hyK : x₀ ^ m ∈ K := K.pow_mem hx₀K m
  have hyC : x₀ ^ m ∈ centralizerMod (pCoreOf 2 H) H K :=
    (centralizerMod (pCoreOf 2 H) H K).pow_mem
      (show x₀ ∈ centralizerMod (pCoreOf 2 H) H K from ⟨hKH hx₀K, hQn (hKH hx₀K), hx₀c⟩) m
  have hU := hkey (x₀ ^ m) hyK hyC.2.2 hmQ
  have hZ : SectionFaithful T (fsuV1 T V) V H K := by
    intro F E hV₁F hFE hEU hFn hEn hnt x hx hxc hxE
    by_contra hxQ
    rw [hK₀] at hx hxc
    obtain ⟨m', hm'3, hm'Q⟩ := exists_pow_three (hx3 x hx hxc) hxQ
    have hy'C := (centralizerMod (pCoreOf 2 H) H K).pow_mem
      (show x ∈ centralizerMod (pCoreOf 2 H) H K from ⟨hKH hx, hQn (hKH hx), hxc⟩) m'
    have hy'K : x ^ m' ∈ K := K.pow_mem hx m'
    have hU' := hkey (x ^ m') hy'K hy'C.2.2 hm'Q
    have hxF : x ∈ Subgroup.normalizer (F : Set G) :=
      hFn (Subgroup.mem_sup_left (le_conjClosure K T hx))
    have hy'T := (centralizerMod F ⊤ E).pow_mem
      (show x ∈ centralizerMod F ⊤ E from ⟨Subgroup.mem_top x, hxF, hxE⟩) m'
    have hle := le_of_trivial_mod hV₁H hUN hUH hV₁U (hKH hy'K) hm'3 hU' hV₁F hFE hEU hy'T.2.1
      hy'T.2.2
    apply hnt
    intro k hk e he
    have heF := hle he
    have hkF : k ∈ Subgroup.normalizer (F : Set G) := hFn (Subgroup.mem_sup_left hk)
    exact F.mul_mem ((Subgroup.mem_normalizer_iff.mp hkF e).mp heF) (F.inv_mem heF)
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirrT := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have hFct := factElem hF hIU
  have hirr' : subM (fsuV1 T V) (conjClosure I H) I ∈
      IrrPlusOn (autIH (fsuV1 T V) I H (conjClosure K T))
        (orbSup (autIH (fsuV1 T V) I H T) (subM (fsuV1 T V) (conjClosure I H) I))
        (autIH (fsuV1 T V) I H T) := hirrT
  have hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G) :=
    K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  have h4 := (F918_4_fine' hF hSQ hK₀ hV₁I hIU W hW hirrU hD310 hD391 hI4 hFine).2
  have hHI : H ≤ Subgroup.normalizer (I : Set G) := by
    rcases h4 with h4 | (⟨hVT, -⟩ | h3)
    · exact h4
    · have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
        intro t ht
        have hst := mem_stabSub_of_eq_orbSup' hVT (actH_mem_autIH_of_mem (I := I) hF hTH ht)
        exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
          (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
          (le_conjClosure I H) ⟨t, hTH ht⟩).mp hst
      rw [hHeq']
      exact sup_le hKI hTI
    · exact (false_of_d310Two_card h3
        (Or.inr ((card_autIH_eq hF hHeq' hZ hV₁I hIU hnt).trans (card_cStar_hat hhat)))).elim
  have hcI : conjClosure I H = I :=
    le_antisymm (conjClosure_le fun _ hh i hi => (Subgroup.mem_normalizer_iff.mp (hHI hh) i).mp hi)
      (le_conjClosure I H)
  have hI := isIrrPlusTilde_of_module hF hV₁I hIU hirrT
  have hcardK : Nat.card (KBar K) = 1330560 := card_cStar_hat hhat
  have hNo : HasNoFaithfulFFModulesMod (conjClosure K T ⊔ T) (pCoreOf 2 H) := by
    rw [← hHeq']
    have hZK : Nat.card (Subgroup.center (KBar K)) = 3 := hhat.2.1
    refine hasNoFaithfulFF_of_kbar h56 hSQ hK hKn hTH hF.sylow_H.2.1 hHKT hq
      (by rw [hZK]; exact ⟨1, rfl⟩) (by rw [hcardK]; norm_num) fun X _ _ hX hL => ?_
    exact false_of_b56List hL (m := 10395) (by decide) (by decide) (by rw [hX, hcardK]; norm_num)
  have h7' := F918_7'' hF hHeq' hZ hV₁I hIU hI hNo
  rw [hcI] at h7'
  have hcomm : ⁅conjClosure V H, conjClosure K T⁆ ⊔ fsuV1 T V = conjClosure V H := by
    refine le_antisymm (sup_le ?_ hV₁U) (hU.symm.le.trans (sup_le_sup_right
      (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr (le_conjClosure K T hyK))) _))
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hF.K₀_le_H.trans hUH)
  have hIUeq : I = conjClosure V H := by
    have hcN : ⁅conjClosure V H, conjClosure K T⁆ ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
      (le_sup_left.trans hcomm.le).trans hUN
    have h2 : tildeOf (fsuV1 T V) (⁅conjClosure V H, conjClosure K T⁆ ⊔ fsuV1 T V) =
        tildeOf (fsuV1 T V) ⁅conjClosure V H, conjClosure K T⁆ := by
      rw [tildeOf_sup' hcN (hV₁U.trans hUN), tildeOf_eq_bot_of_le le_rfl, sup_bot_eq]
    have ht : tildeOf (fsuV1 T V) I = tildeOf (fsuV1 T V) (conjClosure V H) := by
      rw [h7', ← h2, hcomm]
    exact eq_of_secImg_eq hV₁I hV₁U ((le_conjClosure I H).trans
      (hF.conjClosure_le_normalizer_V₁ hIU)) hUN ht
  have hC : centralizerMod (fsuV1 T V) I (conjClosure K T) = fsuV1 T V := by
    refine le_antisymm (fun a ha => ?_) (le_centralizerMod hF.H_le_normalizer_V₁ hF.K₀_le_H hV₁I)
    obtain ⟨haI, -, hac⟩ := ha
    have h1 := (fsuV1 T V).inv_mem (hac _ (le_conjClosure K T hyK))
    have e : (a * x₀ ^ m * a⁻¹ * (x₀ ^ m)⁻¹)⁻¹ = x₀ ^ m * a * (x₀ ^ m)⁻¹ * a⁻¹ := by group
    rw [e] at h1
    exact mem_of_comm_mem hV₁H hUN hUH hV₁U (hKH hyK) hm3 hU (hIU haI) h1
  have hK₀J : conjClosure K T ≤ Subgroup.normalizer (J : Set G) := by rw [hK₀]; exact hKJ
  rcases hI.2.2.2 J hV₁J (hJU.trans hIUeq.ge) hK₀J (hC.le.trans hV₁J) with h | h
  · exact Or.inl (h.trans hC)
  · exact Or.inr (h.trans hIUeq)

end Main

end CFSG.Quasithin.H13.KGFFZ
