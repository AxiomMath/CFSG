module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ug
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22um

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Bar11

variable {M V₀ V : Subgroup G} [hn : ((F11.CTilde M V₀ V).subgroupOf M).Normal]

theorem uc22p22u_mem_barImage11 {Y : Subgroup G} {q : F11.MBar11 M V₀ V} :
    q ∈ F11.barImage11 M V₀ V Y ↔
      ∃ m : ↥M, (m : G) ∈ Y ∧ (QuotientGroup.mk m : F11.MBar11 M V₀ V) = q := by
  unfold F11.barImage11
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩

theorem uc22p22u_mem_barPreimage11 {Xbar : Subgroup (F11.MBar11 M V₀ V)} {x : G} :
    x ∈ F11.barPreimage11 M V₀ V Xbar ↔
      ∃ h : x ∈ M, (QuotientGroup.mk ⟨x, h⟩ : F11.MBar11 M V₀ V) ∈ Xbar := by
  unfold F11.barPreimage11
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem uc22p22u_mk_eq_iff {m m' : ↥M} :
    (QuotientGroup.mk m : F11.MBar11 M V₀ V) = QuotientGroup.mk m' ↔
      ((m⁻¹ * m' : ↥M) : G) ∈ F11.CTilde M V₀ V := by
  rw [QuotientGroup.eq]
  exact Subgroup.mem_subgroupOf

theorem uc22p22u_card_eq_map_mul_inf_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (H : Subgroup X) : Nat.card ↥H = Nat.card ↥(H.map f) * Nat.card ↥(H ⊓ f.ker) := by
  have h := Subgroup.relIndex_mul_card f.ker H
  rw [Subgroup.relIndex_ker, inf_comm] at h
  exact h.symm

theorem uc22p22u_card_eq_barImage11_mul {Y : Subgroup G} (hYM : Y ≤ M) :
    Nat.card ↥Y = Nat.card ↥(F11.barImage11 M V₀ V Y) * Nat.card ↥(Y ⊓ F11.CTilde M V₀ V) := by
  have h := uc22p22u_card_eq_map_mul_inf_ker
    (QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M)) (Y.subgroupOf M)
  have h1 : Nat.card ↥(Y.subgroupOf M) = Nat.card ↥Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv
  have h2 : Y.subgroupOf M ⊓ (QuotientGroup.mk' ((F11.CTilde M V₀ V).subgroupOf M)).ker =
      (Y ⊓ F11.CTilde M V₀ V).subgroupOf M := by
    ext x
    simp [Subgroup.mem_subgroupOf, QuotientGroup.ker_mk']
  have h3 : Nat.card ↥((Y ⊓ F11.CTilde M V₀ V).subgroupOf M) = Nat.card ↥(Y ⊓ F11.CTilde M V₀ V) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hYM)).toEquiv
  rw [h2, h1, h3] at h
  exact h

end Bar11

theorem uc22p22u_tdata (D : Data G) (h116 : R116W D) (h118 : R118W D) {V : Subgroup G}
    (hV : F11.Hyp11 D ⊥ V) [hNorm : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M))
    {Xbar : Subgroup (F11.MBar11 D.M ⊥ V)} [hXn : Xbar.Normal] (hXe : IsElemAbelian p Xbar)
    (hXle : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), (⊤ : Subgroup (F11.MBar11 D.M ⊥ V))⁆)
    {T Z : Subgroup G} (hT : T = P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar)
    (hZ : Z = T ⊓ F11.CTilde D.M ⊥ V) :
    IsPGroup p ↥T ∧ IsCyclic ↥Z ∧ Z ≤ T ∧ ⁅T, T⁆ ≤ Z ∧ ⁅T, Z⁆ = ⊥ ∧ (∀ t ∈ T, t ^ p ∈ Z) ∧
      T ≤ D.M ∧ F11.barImage11 D.M ⊥ V T = Xbar := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPM, -, -⟩ := uc22p22u_sylow_O2p hp hp2 hP
  have hPp : IsPGroup p ↥P := (CFSG.ABGLocalTools.isSylowOf_iff.1 hP).2.1
  have h1 := uc22p22u_r1110_part1 D h118 hV hp hp2 hP
  obtain ⟨hcyc, hcent⟩ := uc22p22u_r1110_part2 D h116 hV hp hp2 hP
  have hTP : T ≤ P := by rw [hT]; exact inf_le_left.trans inf_le_left
  have hTQ : T ≤ P ⊓ ⁅D.M, D.M⁆ := by rw [hT]; exact inf_le_left
  have hTM : T ≤ D.M := hTP.trans hPM
  have hZT : Z ≤ T := by rw [hZ]; exact inf_le_left
  have hZP : Z ≤ P ⊓ F11.CTilde D.M ⊥ V := by rw [hZ]; exact le_inf (inf_le_left.trans hTP) inf_le_right
  have hmemT : ∀ t ∈ T, ∃ h : t ∈ D.M, (QuotientGroup.mk ⟨t, h⟩ : F11.MBar11 D.M ⊥ V) ∈ Xbar := by
    intro t ht
    rw [hT] at ht
    exact uc22p22u_mem_barPreimage11.1 ht.2
  refine ⟨hPp.to_le hTP, ?_, hZT, ?_, ?_, ?_, hTM, ?_⟩
  · haveI := hcyc
    exact isCyclic_of_injective (Subgroup.inclusion hZP) (Subgroup.inclusion_injective hZP)
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    obtain ⟨haM, ha'⟩ := hmemT a ha
    obtain ⟨hbM, hb'⟩ := hmemT b hb
    have hc := hXe.1.is_comm.comm ⟨_, ha'⟩ ⟨_, hb'⟩
    have hc' : (QuotientGroup.mk ⟨a, haM⟩ : F11.MBar11 D.M ⊥ V) * QuotientGroup.mk ⟨b, hbM⟩ =
        QuotientGroup.mk ⟨b, hbM⟩ * QuotientGroup.mk ⟨a, haM⟩ := congrArg Subtype.val hc
    have h2 : (QuotientGroup.mk ⁅(⟨a, haM⟩ : ↥D.M), ⟨b, hbM⟩⁆ : F11.MBar11 D.M ⊥ V) = 1 := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply]
      exact commutatorElement_eq_one_iff_commute.2 hc'
    have h3 : ⁅a, b⁆ ∈ F11.CTilde D.M ⊥ V := by
      have := (QuotientGroup.eq_one_iff _).1 h2
      simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using this
    rw [hZ]
    refine ⟨?_, h3⟩
    have : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := rfl
    rw [this]
    exact T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb)
  · exact le_bot_iff.1 ((Subgroup.commutator_mono hTQ hZP).trans hcent.le)
  · intro t ht
    obtain ⟨htM, ht'⟩ := hmemT t ht
    have h2 : (QuotientGroup.mk (⟨t, htM⟩ ^ p : ↥D.M) : F11.MBar11 D.M ⊥ V) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hXe.2 _ ht'
    have h3 : t ^ p ∈ F11.CTilde D.M ⊥ V := by
      have := (QuotientGroup.eq_one_iff _).1 h2
      simpa [Subgroup.mem_subgroupOf] using this
    rw [hZ]
    exact ⟨T.pow_mem ht p, h3⟩
  · apply le_antisymm
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
      obtain ⟨hmM, hm'⟩ := hmemT _ hm
      exact hm'
    · intro q hq
      have hq1 : q ∈ pCoreOf p ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), ⊤⁆ :=
        uc22p22u_le_pCoreOf Xbar _ (CFSG.Open.IsElemAbelian.isPGroup hXe) hXle hq
      rw [h1] at hq1
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq1
      refine uc22p22u_mem_barImage11.2 ⟨m, ?_, rfl⟩
      rw [hT]
      exact ⟨hm, uc22p22u_mem_barPreimage11.2 ⟨m.2, hq⟩⟩

theorem uc22p22u_r1110_part3a (D : Data G) (h116 : R116W D) (h118 : R118W D) {V : Subgroup G}
    (hV : F11.Hyp11 D ⊥ V) [hNorm : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) {n : ℕ} (hn : 1 < n)
    {Xbar : Subgroup (F11.MBar11 D.M ⊥ V)} [hXn : Xbar.Normal] (hXe : IsElemAbelian p Xbar)
    (hXc : Nat.card Xbar = p ^ n)
    (hXle : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), (⊤ : Subgroup (F11.MBar11 D.M ⊥ V))⁆) :
    (∀ x ∈ F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar), x ^ p = 1) ∧
      (IsMulCommutative (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar)) ∨
        (Nat.card ↥⁅F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar),
            F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar)⁆ = p ∧
          ⁅F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar),
              F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar)⁆ ≤
            F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar) ⊓
              centralizer ((F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar) :
                Subgroup G) : Set G))) ∧
      p ^ n ≤ Nat.card (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar)) ∧
      n / 2 + 1 ≤
        CFSG.Open.pRank p (F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar)) := by
  obtain ⟨hTp, hZc, hZT, hcomm, hcent, hpow, hTM, hbar⟩ := uc22p22u_tdata D h116 h118 hV hp hp2 hP hXe hXle
    (T := P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar)
    (Z := (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar) ⊓ F11.CTilde D.M ⊥ V) rfl rfl
  have hcard := uc22p22u_card_eq_barImage11_mul (M := D.M) (V₀ := ⊥) (V := V) hTM
  rw [hbar, hXc] at hcard
  exact uc22p22u_twostep_bundle hp hp2 hTp hZc hZT hcomm hcent hpow hn hcard

theorem uc22p22u_mem_CElt_bot {M : Subgroup G} {v m : G} :
    m ∈ F11.CElt M ⊥ v ↔ m ∈ M ∧ m * v = v * m := by
  constructor
  · rintro ⟨hm, -, h⟩
    refine ⟨hm, ?_⟩
    rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h
  · rintro ⟨hm, h⟩
    refine ⟨hm, ?_, ?_⟩
    · rw [mem_normalizer_iff]
      intro y
      simp [Subgroup.mem_bot]
    · rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact h

theorem uc22p22u_mem_normalizer_Omega1p {p : ℕ} {T : Subgroup G} {g : G}
    (hg : g ∈ normalizer (T : Set G)) :
    g ∈ normalizer ((F11.Omega1p p T : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ normalizer (T : Set G) →
      ∀ x ∈ F11.Omega1p p T, g' * x * g'⁻¹ ∈ F11.Omega1p p T := by
    intro g' hg' x hx
    refine Subgroup.closure_induction (p := fun x _ => g' * x * g'⁻¹ ∈ F11.Omega1p p T)
      ?_ ?_ ?_ ?_ hx
    · rintro y ⟨hyT, hyp⟩
      refine Subgroup.subset_closure ⟨(mem_normalizer_iff.1 hg' y).1 hyT, ?_⟩
      rw [conj_pow, hyp]
      simp
    · simp
    · intro a b _ _ ha hb
      have : g' * (a * b) * g'⁻¹ = (g' * a * g'⁻¹) * (g' * b * g'⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      have : g' * a⁻¹ * g'⁻¹ = (g' * a * g'⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem uc22p22u_uniqueMax_mono (D : Data G) {E X : Subgroup G} (hEX : E ≤ X) (hXM : X ≤ D.M)
    (hE : UniqueMax D.M E) : UniqueMax D.M X := by
  unfold UniqueMax at hE ⊢
  refine Set.Subset.antisymm ?_ ?_
  · intro N hN
    have : N ∈ calMOf E := ⟨hN.1, hEX.trans hN.2⟩
    rwa [hE] at this
  · rintro N rfl
    exact ⟨D.maxLocal, hXM⟩

theorem uc22p22u_exists_elemAbelian_omega1 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S Z : Subgroup G}
    (hS : IsPGroup p ↥S) (hZc : IsCyclic ↥Z) (hZS : Z ≤ S) (hcomm : ⁅S, S⁆ ≤ Z) (hcent : ⁅S, Z⁆ = ⊥)
    (hpow : ∀ t ∈ S, t ^ p ∈ Z) (hcard : p ^ 2 * Nat.card ↥Z ≤ Nat.card ↥S) :
    ∃ E : Subgroup G, E ≤ F11.Omega1p p S ∧ IsElemAbelian p E ∧ Nat.card ↥E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hS
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 (hS.to_le hZS)
  have hab : 2 + b ≤ a := by
    rw [ha, hb, ← pow_add] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  have hcard' : Nat.card ↥S = p ^ (a - b) * Nat.card ↥Z := by
    rw [ha, hb, ← pow_add]
    congr 1
    omega
  obtain ⟨hexp, -, hcardY, -⟩ := uc22p22u_twostep_bundle hp hp2 hS hZc hZS hcomm hcent hpow
    (n := a - b) (by omega) hcard'
  have hYS : F11.Omega1p p S ≤ S := (Subgroup.closure_le S).2 fun x hx => hx.1
  have hYp : IsPGroup p ↥(F11.Omega1p p S) := hS.to_le hYS
  have hnc : ¬ IsCyclic ↥(F11.Omega1p p S) := by
    intro hc
    have h1 : Monoid.exponent ↥(F11.Omega1p p S) ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hexp g.1 g.2)
    rw [IsCyclic.exponent_eq_card] at h1
    have h2 := Nat.le_of_dvd hp.pos h1
    have h3 : p ^ 2 ≤ p ^ (a - b) := Nat.pow_le_pow_right hp.pos (by omega)
    have h4 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  exact uc22p22u_exists_elemAbelian_sq hp hp2 hYp hnc

theorem uc22p22u_mem_normalizer_commutator {M : Subgroup G} {g : G} (hg : g ∈ M) :
    g ∈ normalizer ((⁅M, M⁆ : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ M → ∀ x ∈ ⁅M, M⁆, g' * x * g'⁻¹ ∈ ⁅M, M⁆ := by
    intro g' hg' x hx
    rw [Subgroup.commutator_def] at hx ⊢
    refine Subgroup.closure_induction (p := fun x _ => g' * x * g'⁻¹ ∈ Subgroup.closure
      {g | ∃ g₁ ∈ M, ∃ g₂ ∈ M, ⁅g₁, g₂⁆ = g}) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨a, ha, b, hb, rfl⟩
      refine Subgroup.subset_closure ⟨g' * a * g'⁻¹, M.mul_mem (M.mul_mem hg' ha) (M.inv_mem hg'),
        g' * b * g'⁻¹, M.mul_mem (M.mul_mem hg' hb) (M.inv_mem hg'), ?_⟩
      simp only [commutatorElement_def]
      group
    · simp
    · intro a b _ _ ha hb
      have : g' * (a * b) * g'⁻¹ = (g' * a * g'⁻¹) * (g' * b * g'⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      have : g' * a⁻¹ * g'⁻¹ = (g' * a * g'⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ha
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (M.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem uc22p22u_mem_normalizer_barPreimage11 {M V₀ V : Subgroup G}
    [((F11.CTilde M V₀ V).subgroupOf M).Normal] {Xbar : Subgroup (F11.MBar11 M V₀ V)} [hXn : Xbar.Normal]
    {g : G} (hg : g ∈ M) : g ∈ normalizer ((F11.barPreimage11 M V₀ V Xbar : Subgroup G) : Set G) := by
  have key : ∀ g' : G, g' ∈ M → ∀ x ∈ F11.barPreimage11 M V₀ V Xbar,
      g' * x * g'⁻¹ ∈ F11.barPreimage11 M V₀ V Xbar := by
    intro g' hg' x hx
    obtain ⟨hxM, hx'⟩ := uc22p22u_mem_barPreimage11.1 hx
    refine uc22p22u_mem_barPreimage11.2 ⟨M.mul_mem (M.mul_mem hg' hxM) (M.inv_mem hg'), ?_⟩
    have : (⟨g' * x * g'⁻¹, M.mul_mem (M.mul_mem hg' hxM) (M.inv_mem hg')⟩ : ↥M) =
        ⟨g', hg'⟩ * ⟨x, hxM⟩ * ⟨g', hg'⟩⁻¹ := rfl
    rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hXn.conj_mem _ hx' _
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (M.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem uc22p22u_not_isCyclic_of_card_sq {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : Nat.card ↥E = p ^ 2) : ¬ IsCyclic ↥E := by
  intro hc
  have h1 : Monoid.exponent ↥E ∣ p :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hE.2 g.1 g.2)
  rw [IsCyclic.exponent_eq_card, hcard] at h1
  have h2 := Nat.le_of_dvd hp.pos h1
  have h3 : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem uc22p22u_r1110_part3b (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h116 : R116W D) (h118 : R118W D) {V : Subgroup G}
    (hV : F11.Hyp11 D ⊥ V) [hNorm : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M))
    {Xbar : Subgroup (F11.MBar11 D.M ⊥ V)} [hXn : Xbar.Normal] (hXe : IsElemAbelian p Xbar)
    (hXle : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), (⊤ : Subgroup (F11.MBar11 D.M ⊥ V))⁆)
    (hσ : D.sig = D.sig1) {v : G} (hvV : v ∈ V)
    (hrank : 1 < CFSG.Open.pRank p (Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v))) :
    UniqueMax D.M (D.M ⊓ centralizer ({v} : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hVc := uc22p22u_cTilde_bot D.M V
  obtain ⟨hPM, -, -⟩ := uc22p22u_sylow_O2p hp hp2 hP
  set T : Subgroup G := P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M ⊥ V Xbar with hT
  set Z : Subgroup G := T ⊓ F11.CTilde D.M ⊥ V with hZ
  obtain ⟨hTp, hZc, hZT, hcomm, hcent, hpow, hTM, hbar⟩ :=
    uc22p22u_tdata D h116 h118 hV hp hp2 hP hXe hXle hT hZ
  have hX₀v : F11.CTilde D.M ⊥ V ≤ centralizer ({v} : Set G) := by
    rw [hVc]
    intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subgroup.mem_centralizer_iff.1 hx.2 h hvV
  set S : Subgroup G := T ⊓ centralizer ({v} : Set G) with hS
  have hST : S ≤ T := inf_le_left
  have hZS : Z ≤ S := le_inf hZT (inf_le_right.trans hX₀v)
  have hSp : IsPGroup p ↥S := hTp.to_le hST
  have hScomm : ⁅S, S⁆ ≤ Z := (Subgroup.commutator_mono hST hST).trans hcomm
  have hScent : ⁅S, Z⁆ = ⊥ := le_bot_iff.1 ((Subgroup.commutator_mono hST le_rfl).trans hcent.le)
  have hSpow : ∀ t ∈ S, t ^ p ∈ Z := fun t ht => hpow t ht.1
  have hSZ : S ⊓ F11.CTilde D.M ⊥ V = Z := by
    ext x
    constructor
    · rintro ⟨⟨hxT, -⟩, hx⟩
      exact ⟨hxT, hx⟩
    · rintro ⟨hxT, hx⟩
      exact ⟨⟨hxT, hX₀v hx⟩, hx⟩
  have hSW : F11.barImage11 D.M ⊥ V S =
      Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v) := by
    apply le_antisymm
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
      refine ⟨hbar ▸ uc22p22u_mem_barImage11.2 ⟨m, hm.1, rfl⟩, uc22p22u_mem_barImage11.2 ⟨m, ?_, rfl⟩⟩
      exact uc22p22u_mem_CElt_bot.2 ⟨m.2, (Subgroup.mem_centralizer_iff.1 hm.2 v rfl).symm⟩
    · rintro q ⟨hqX, hqC⟩
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 (hbar ▸ hqX)
      obtain ⟨m', hm', hmm'⟩ := uc22p22u_mem_barImage11.1 hqC
      obtain ⟨-, hm'c⟩ := uc22p22u_mem_CElt_bot.1 hm'
      have h1 : ((m'⁻¹ * m : ↥D.M) : G) ∈ F11.CTilde D.M ⊥ V := uc22p22u_mk_eq_iff.1 hmm'
      have h2 : ((m'⁻¹ * m : ↥D.M) : G) * v = v * ((m'⁻¹ * m : ↥D.M) : G) :=
        Subgroup.mem_centralizer_iff.1 (hX₀v h1) v rfl |>.symm
      have h3 : (m : G) = (m' : G) * ((m'⁻¹ * m : ↥D.M) : G) := by simp
      refine uc22p22u_mem_barImage11.2 ⟨m, ⟨hm, ?_⟩, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rw [h3]
      calc h * ((m' : G) * ((m'⁻¹ * m : ↥D.M) : G)) = (h * (m' : G)) * ((m'⁻¹ * m : ↥D.M) : G) := by
            rw [mul_assoc]
        _ = ((m' : G) * h) * ((m'⁻¹ * m : ↥D.M) : G) := by rw [← hm'c]
        _ = (m' : G) * (h * ((m'⁻¹ * m : ↥D.M) : G)) := by rw [mul_assoc]
        _ = (m' : G) * (((m'⁻¹ * m : ↥D.M) : G) * h) := by rw [← h2]
        _ = (m' : G) * ((m'⁻¹ * m : ↥D.M) : G) * h := by rw [mul_assoc]
  have hcardS := uc22p22u_card_eq_barImage11_mul (M := D.M) (V₀ := ⊥) (V := V) (hST.trans hTM)
  rw [hSW, hSZ] at hcardS
  have hS2 : p ^ 2 * Nat.card ↥Z ≤ Nat.card ↥S := by
    obtain ⟨E₀, hE₀W, hE₀e, hE₀c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v))
    have h1 : p ^ 2 ≤ Nat.card ↥(Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v)) := by
      calc p ^ 2 ≤ p ^ CFSG.Open.pRank p (Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v)) :=
            Nat.pow_le_pow_right hp.pos hrank
        _ = Nat.card ↥E₀ := hE₀c.symm
        _ ≤ _ := Subgroup.card_le_of_le hE₀W
    rw [hcardS]
    exact Nat.mul_le_mul_right _ h1
  obtain ⟨E, hEΩ, hEe, hEc⟩ := uc22p22u_exists_elemAbelian_omega1 hp hp2 hSp hZc hZS hScomm hScent
    hSpow hS2
  have hΩS : F11.Omega1p p S ≤ S := (Subgroup.closure_le S).2 fun x hx => hx.1
  have hΩT : F11.Omega1p p S ≤ F11.Omega1p p T :=
    Subgroup.closure_mono fun x hx => ⟨hST hx.1, hx.2⟩
  have hES : E ≤ S := hEΩ.trans hΩS
  have hEM : E ≤ D.M := hES.trans (hST.trans hTM)
  have hEC : E ≤ D.M ⊓ centralizer ({v} : Set G) := le_inf hEM (hES.trans inf_le_right)
  have hEp : IsPGroup p ↥E := CFSG.Open.IsElemAbelian.isPGroup hEe
  have hEnc : ¬ IsCyclic ↥E := uc22p22u_not_isCyclic_of_card_sq hp hEe hEc
  have hΓ : rankThreeGamma 1 p E ≤ D.M ∨ p ∈ D.sig := by
    by_cases hpσ : p ∈ D.sig
    · exact Or.inr hpσ
    refine Or.inl ?_
    obtain ⟨p₁, hp₁⟩ := hSig.nonempty
    have hp₁1 : p₁ ∈ D.sig1 := hσ ▸ hp₁
    have hsp := hSig.sig1_sp p₁ hp₁1
    obtain ⟨hp₁pr, hp₁2⟩ := D.sig_prime p₁ hp₁
    have hp₁p : p₁ ≠ p := fun h => hpσ (h ▸ hp₁)
    set Y : Subgroup G := F11.Omega1p p T with hY
    have hYT : Y ≤ T := (Subgroup.closure_le T).2 fun x hx => hx.1
    have hYM : Y ≤ D.M := hYT.trans hTM
    have hYp : IsPGroup p ↥Y := hTp.to_le hYT
    have hEY : E ≤ Y := hEΩ.trans hΩT
    have hYnc : ¬ IsCyclic ↥Y := by
      intro hc
      haveI := hc
      exact hEnc (isCyclic_of_injective (Subgroup.inclusion hEY) (Subgroup.inclusion_injective hEY))
    have hclT : ⁅⁅T, T⁆, T⁆ = ⊥ := by
      rw [eq_bot_iff, ← hcent]
      exact (Subgroup.commutator_mono hcomm le_rfl).trans (by rw [Subgroup.commutator_comm])
    have hYexp : ∀ x ∈ Y, x ^ p = 1 := uc22p22u_omega1p_exponent hp hp2 hTp hclT
    have hYcl : ⁅⁅Y, Y⁆, Y⁆ = ⊥ :=
      le_bot_iff.1 ((Subgroup.commutator_mono (Subgroup.commutator_mono hYT hYT) hYT).trans hclT.le)
    have hNY : D.M ⊓ normalizer (P : Set G) ≤ D.M ⊓ normalizer (Y : Set G) := by
      refine le_inf inf_le_left fun g hg => ?_
      have hgT : g ∈ normalizer (T : Set G) := by
        rw [hT]
        have hgP : g ∈ normalizer (P : Set G) := hg.2
        have hgM : g ∈ D.M := hg.1
        have h1 := uc22p22u_mem_normalizer_commutator hgM
        have h2 := uc22p22u_mem_normalizer_barPreimage11 (Xbar := Xbar) hgM
        refine mem_normalizer_iff.2 fun x => ?_
        constructor
        · rintro ⟨⟨hxP, hxc⟩, hxX⟩
          exact ⟨⟨(mem_normalizer_iff.1 hgP x).1 hxP, (mem_normalizer_iff.1 h1 x).1 hxc⟩,
            (mem_normalizer_iff.1 h2 x).1 hxX⟩
        · rintro ⟨⟨hxP, hxc⟩, hxX⟩
          exact ⟨⟨(mem_normalizer_iff.1 hgP x).2 hxP, (mem_normalizer_iff.1 h1 x).2 hxc⟩,
            (mem_normalizer_iff.1 h2 x).2 hxX⟩
      exact uc22p22u_mem_normalizer_Omega1p hgT
    haveI : (CFSG.pCore p (Bar2 D.M)).Normal := CFSG.pCore_normal
    have hOn : D.M ≤ normalizer ((F11.O2p p D.M : Subgroup G) : Set G) :=
      uc22p22u_barPreimage_normalizes (D := CFSG.pCore p (Bar2 D.M))
    have hp₁O : ¬ p₁ ∣ Nat.card ↥(F11.O2p p D.M) := by
      have hcard : Nat.card ↥(F11.O2p p D.M) =
          Nat.card ↥(pCoreOf 2 D.M) * Nat.card ↥(CFSG.pCore p (Bar2 D.M)) :=
        uc22p22u_card_barPreimage D.M (CFSG.pCore p (Bar2 D.M))
      rw [hcard]
      intro hd
      rcases (Nat.Prime.dvd_mul hp₁pr).1 hd with h | h
      · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (uc22p21c_isPGroup_pCoreOf D.M)
        rw [hk] at h
        exact hp₁2 ((Nat.prime_dvd_prime_iff_eq hp₁pr Nat.prime_two).1 (hp₁pr.dvd_of_dvd_pow h))
      · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M))
        rw [hk] at h
        exact hp₁p ((Nat.prime_dvd_prime_iff_eq hp₁pr hp).1 (hp₁pr.dvd_of_dvd_pow h))
    have hrk := uc22p22u_pRank_le_normalizer_sylow hp₁pr hp (uc22p21c_barPreimage_le D.M _) hOn hP hp₁O
    have hrk' : CFSG.Open.pRank p₁ (D.M ⊓ normalizer (Y : Set G)) ≤ CFSG.Open.pRank p₁ D.M :=
      CFSG.SectionRank.pRank_mono hp₁pr.one_lt inf_le_left
    have hrk'' : CFSG.Open.pRank p₁ (D.M ⊓ normalizer (P : Set G)) ≤
        CFSG.Open.pRank p₁ (D.M ⊓ normalizer (Y : Set G)) :=
      CFSG.SectionRank.pRank_mono hp₁pr.one_lt hNY
    have hthree : 3 ≤ CFSG.Open.pRank p₁ D.M := hSig.three_le p₁ hp₁
    have hΓY := h77 hσ.subset p₁ hp₁ hp₁2 hsp p hp hp2 hpσ Y hYM hYp hYnc hYexp hYcl (by omega)
      (le_antisymm (hrk.trans hrk'') hrk')
    exact (uc22p22u_gamma_mono hEY).trans hΓY
  exact uc22p22u_uniqueMax_mono D hEC inf_le_left
    (uc22p22u_uniqueMax_of_noncyclic D h61 h63 hp hp2 hEM hEp hEnc hΓ)

end CFSG.LocalAnalysis.UniquenessCase.UC22
