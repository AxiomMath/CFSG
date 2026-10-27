module

public import CFSG.Quasithin.Background.HSL3RepTw
public import CFSG.Quasithin.Background.HSecQuot
public import CFSG.Quasithin.Vol2.Ch7Sec77KQuot
public import CFSG.Quasithin.Vol2.Ch7Sec77L3C

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.Quasithin.H.SL3Rep CFSG.Quasithin.H.SecQ CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

@[expose] noncomputable def rhoEquivSL : SL32 ≃* ↥(pairSL (ZMod 2)) :=
  (MonoidHom.ofInjective SL3One.rho_injective).trans (MulEquiv.subgroupCongr SL3One.range_rho)

theorem swapAut_rho_conj (y : SL32) :
    swapAut (ZMod 2) * SL3One.rho y * (swapAut (ZMod 2))⁻¹ = SL3One.rho (tauT y) := by
  have h2 : dualGL (specialLinearGroupEquivStatedSL 3 (ZMod 2) y : GL (Fin 3) (ZMod 2)) =
      (specialLinearGroupEquivStatedSL 3 (ZMod 2) (tauT y) : GL (Fin 3) (ZMod 2)) := by
    apply Units.ext
    rw [coe_dualGL, specialLinearGroupEquivStatedSL_coe, coe_tauT, ← Subgroup.coe_inv, ← map_inv,
      specialLinearGroupEquivStatedSL_coe]
  exact (swapAut_conj _).trans (congrArg pairHom h2)

namespace Setup

variable {S : Setup T L I} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem coord_mem_pairSL (hc : S.Coord θ e) (l : ↥L) :
    congrHom e (convI S.hV ⟨l, S.L_le_normalizer_V l.2⟩) ∈ pairSL (ZMod 2) := by
  rw [← hc.he]
  have hl : (l : G) ∈ fsuL0 T L := by
    rw [← S.hL]
    exact l.2
  exact ⟨_, convI_mem_autI S.hV hl _, rfl⟩

@[expose] noncomputable def lam (hc : S.Coord θ e) : ↥L →* SL32 :=
  rhoEquivSL.symm.toMonoidHom.comp
    (((congrHom e).comp ((convI S.hV).comp (Subgroup.inclusion S.L_le_normalizer_V))).codRestrict
      (pairSL (ZMod 2)) fun l => coord_mem_pairSL hc l)

theorem rho_lam (hc : S.Coord θ e) (l : ↥L) :
    SL3One.rho (lam hc l) = congrHom e (convI S.hV ⟨l, S.L_le_normalizer_V l.2⟩) :=
  congrArg Subtype.val (rhoEquivSL.apply_symm_apply _)

theorem lam_surjective (hc : S.Coord θ e) : Function.Surjective (lam hc) := by
  intro g
  have hg : SL3One.rho g ∈ (autI S.hV (fsuL0 T L)).map (congrHom e) := by
    rw [hc.he]
    exact SL3One.rho_mem_pairSL g
  obtain ⟨φ, hφ, hφg⟩ := hg
  obtain ⟨⟨l, hlN⟩, hlL, rfl⟩ := (mem_autI S.hV).1 hφ
  have hlL' : l ∈ L := by
    rw [S.hL]
    exact hlL
  exact ⟨⟨l, hlL'⟩, SL3One.rho_injective ((rho_lam hc _).trans hφg)⟩

theorem lam_eq_one (hc : S.Coord θ e) {l : ↥L} (h : lam hc l = 1) :
    (l : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  have h1 := rho_lam hc l
  rw [h, map_one] at h1
  exact (convI_eq_one_iff S.hV _).1 (congrHom_injective e (h1.symm.trans (map_one _).symm))

theorem lam_th (hc : S.Coord θ e) : lam hc ⟨θ, hc.mem⟩ = S77.th0 :=
  SL3One.rho_injective ((rho_lam hc _).trans hc.hθ)

theorem exists_twist_lam (hc : S.Coord θ e) : ∃ t ∈ T, ∃ g₁ : SL32, ∀ (l : ↥L)
    (h : t * l * t⁻¹ ∈ L), lam hc ⟨t * l * t⁻¹, h⟩ = tauT (g₁ * lam hc l * g₁⁻¹) := by
  obtain ⟨t, htT, g₁, hg₁⟩ := S.exists_swap hc
  refine ⟨t, htT, g₁, fun l h => SL3One.rho_injective ?_⟩
  have htN : t ∈ Subgroup.normalizer (fsuV T I : Set G) := S.T_le_normalizer_V htT
  rw [rho_lam, ← swapAut_rho_conj]
  show congrHom e (convI S.hV (⟨t, htN⟩ * ⟨l, S.L_le_normalizer_V l.2⟩ * ⟨t, htN⟩⁻¹)) = _
  simp only [map_mul, map_inv]
  rw [hg₁ htN, ← rho_lam hc l]
  have hconj : ∀ a b c : MulAut (PairMod (ZMod 2)),
      a * b * c * (a * b)⁻¹ = a * (b * c * b⁻¹) * a⁻¹ := fun a b c => by group
  exact hconj _ _ _

theorem pCoreOf_L_le_Q (S : Setup T L I) :
    pCoreOf 2 L ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← S.pCoreOf_LT]
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) ?_
    (pCoreOf_isPGroup 2 L)
  exact sup_le (le_normalizer_pCoreOf 2 L)
    (S.T_le_normalizer_L.trans (normalizer_le_normalizer_pCoreOf 2 L))

theorem relIndex_th_or_of_chief
    (hc : S.Coord θ e)
    {A B : Subgroup G} (hBA : B < A) (hAQ : A ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G))
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hTA : T ≤ Subgroup.normalizer (A : Set G))
    (hLB : L ≤ Subgroup.normalizer (B : Set G)) (hTB : T ≤ Subgroup.normalizer (B : Set G))
    (hirr : ∀ D : Subgroup G, B ≤ D → D ≤ A → L ⊔ T ≤ Subgroup.normalizer (D : Set G) →
      D = B ∨ D = A) :
    (Subgroup.centralizer ({θ} : Set G)).relIndex A =
        (Subgroup.centralizer ({θ} : Set G)).relIndex B ∨
      16 * (Subgroup.centralizer ({θ} : Set G)).relIndex B ≤
        (Subgroup.centralizer ({θ} : Set G)).relIndex A := by
  classical
  set C := Subgroup.centralizer ({θ} : Set G) with hC
  have hXA : L ⊔ T ≤ Subgroup.normalizer (A : Set G) := sup_le hLA hTA
  have hXB : L ⊔ T ≤ Subgroup.normalizer (B : Set G) := sup_le hLB hTB
  have hYX : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ L ⊔ T :=
    inf_le_left.trans le_sup_right
  have hAB : A ≤ Subgroup.normalizer (B : Set G) := hAQ.trans (inf_le_left.trans hTB)
  have hB2 : IsPGroup 2 B := S.isPGroup_Q.to_le (hBA.le.trans hAQ)
  have hθL : θ ∈ L := hc.mem
  have hXL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer S.T_le_normalizer_L
  rcases hirr (SecQ.centSub A B L hAB) (SecQ.le_centSub hBA.le hAB hLB) (SecQ.centSub_le hAB)
    (SecQ.le_normalizer_centSub hAB hXA hXB hXL) with hD | hD
  ·
    right
    have hN : (B.subgroupOf A).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBA.le).2 hAB
    have hEA := SecQ.isElementaryAbelian_of_irr hBA.le hAB hXA hXB hYX S.LT_le_normalizer_Q
      S.isPGroup_Q hAQ hBA hirr
    have hQtriv := SecQ.comm_mem_of_irr hBA.le hAB hXA hXB hYX S.LT_le_normalizer_Q S.isPGroup_Q
      (S.isPGroup_Q.to_le hAQ) hBA hirr
    let ψ : ↥L →* MulAut (↥A ⧸ B.subgroupOf A) :=
      SecQ.conjHom.comp (Subgroup.inclusion (le_inf hLA hLB))
    have hψmk : ∀ (l : ↥L) (a : ↥A),
        ψ l (QuotientGroup.mk a) = QuotientGroup.mk (SecQ.conjA (hLA l.2) a) := fun l a =>
      SecQ.conjHom_mk _ a
    have hker : (lam hc).ker ≤ ψ.ker := by
      intro l hl
      rw [MonoidHom.mem_ker] at hl ⊢
      have hlQ : (l : G) ∈ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
        S.pCoreOf_L_le_Q (inf_centralizer_L_le hc ⟨l.2, lam_eq_one hc hl⟩)
      ext w
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective w
      rw [hψmk, MulAut.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have h1 := hQtriv l hlQ (a : G)⁻¹ (A.inv_mem a.2)
      have e1 : (((SecQ.conjA (hLA l.2) a)⁻¹ * a : ↥A) : G) =
          l * (a : G)⁻¹ * (l : G)⁻¹ * (a : G)⁻¹⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, SecQ.coe_conjA]
        group
      rw [e1]
      exact h1
    let φ : SL32 →* MulAut (↥A ⧸ B.subgroupOf A) :=
      (QuotientGroup.lift (lam hc).ker ψ hker).comp
        (QuotientGroup.quotientKerEquivOfSurjective (lam hc) (lam_surjective hc)).symm.toMonoidHom
    have hφl : ∀ l : ↥L, φ (lam hc l) = ψ l := by
      intro l
      have h1 : (QuotientGroup.quotientKerEquivOfSurjective (lam hc) (lam_surjective hc)).symm
          (lam hc l) = QuotientGroup.mk l := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      show QuotientGroup.lift (lam hc).ker ψ hker
        ((QuotientGroup.quotientKerEquivOfSurjective (lam hc) (lam_surjective hc)).symm
          (lam hc l)) = ψ l
      rw [h1, QuotientGroup.lift_mk]
    obtain ⟨t, htT, g₁, htw⟩ := exists_twist_lam hc
    have htA := hTA htT
    have htB := hTB htT
    have htL : ∀ l ∈ L, t * l * t⁻¹ ∈ L := fun l hl =>
      (Subgroup.mem_normalizer_iff.1 (S.T_le_normalizer_L htT) l).1 hl
    have hτ : ∀ g w, SecQ.conjW htA htB (φ g w) =
        φ (tauT (g₁ * g * g₁⁻¹)) (SecQ.conjW htA htB w) := by
      intro g w
      obtain ⟨l, rfl⟩ := lam_surjective hc g
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective w
      rw [← htw l (htL l l.2), hφl, hφl, hψmk, SecQ.conjW_mk, SecQ.conjW_mk, hψmk]
      congr 1
      apply Subtype.ext
      simp only [SecQ.coe_conjA]
      group
    have hfree : ∀ w, (∀ g, φ g w = w) → w = 1 := by
      intro w hw
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective w
      rw [QuotientGroup.eq_one_iff]
      have haD : (a : G) ∈ SecQ.centSub A B L hAB := ⟨a.2, fun y hy => by
        have h1 := hw (lam hc ⟨y, hy⟩)
        rw [hφl, hψmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
        have h2 : (y * a * y⁻¹ : G)⁻¹ * a ∈ B := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, SecQ.coe_conjA] at h1
          exact h1
        have e2 : y * (a : G) * y⁻¹ * (a : G)⁻¹ =
            (a : G) * ((y * a * y⁻¹ : G)⁻¹ * a)⁻¹ * (a : G)⁻¹ := by group
        rw [e2]
        exact (Subgroup.mem_normalizer_iff.1 (hAB a.2) _).1 (B.inv_mem h2)⟩
      rw [hD] at haD
      exact haD
    have hWnt : Nontrivial (↥A ⧸ B.subgroupOf A) := by
      obtain ⟨a₀, ha₀A, ha₀B⟩ := IsConcreteLE.exists_of_lt hBA
      exact ⟨⟨QuotientGroup.mk ⟨a₀, ha₀A⟩, 1,
        fun h => ha₀B ((QuotientGroup.eq_one_iff (⟨a₀, ha₀A⟩ : ↥A)).1 h)⟩⟩
    have key := sixteen_mul_card_fix_le_of_mulAut φ hfree g₁ (SecQ.conjW htA htB) hτ
    have hφθ : ∀ w, φ S77.th0 w = SecQ.conjW (hLA hθL) (hLB hθL) w := by
      intro w
      rw [← lam_th hc, hφl]
      rfl
    have hfix : B.relIndex (C ⊓ A) ≤
        Nat.card {w : ↥A ⧸ B.subgroupOf A // φ S77.th0 w = w} :=
      (SecQ.relIndex_le_card_fix (hLA hθL) (hLB hθL)).trans (le_of_eq (Nat.card_congr
        (Equiv.subtypeEquivRight fun w => by rw [hφθ])))
    have hW : Nat.card (↥A ⧸ B.subgroupOf A) = B.relIndex A := rfl
    rw [hW] at key
    have hmul := SecQ.relIndex_mul_eq hBA.le C
    have hpos : 0 < B.relIndex (C ⊓ A) := Nat.pos_of_ne_zero (by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite)
    have h1 : B.relIndex (C ⊓ A) * (16 * C.relIndex B) ≤ B.relIndex (C ⊓ A) * C.relIndex A :=
      calc B.relIndex (C ⊓ A) * (16 * C.relIndex B)
          = (16 * B.relIndex (C ⊓ A)) * C.relIndex B := by ring
        _ ≤ (16 * Nat.card {w : ↥A ⧸ B.subgroupOf A // φ S77.th0 w = w}) * C.relIndex B :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hfix)
        _ ≤ B.relIndex A * C.relIndex B := Nat.mul_le_mul_right _ key
        _ = B.relIndex (C ⊓ A) * C.relIndex A := by rw [hmul]; ring
    exact Nat.le_of_mul_le_mul_left h1 hpos
  ·
    left
    refine le_antisymm (relIndex_le_of_forall_conj fun a ha => ?_)
      (relIndex_le_of_forall_conj fun b hb => ⟨b, hBA.le hb, rfl⟩)
    have haD : a ∈ SecQ.centSub A B L hAB := by
      rw [hD]
      exact ha
    exact exists_conj_eq_of_comm_mem hB2 hc.odd (hLB hθL) (hAB ha) fun n => by
      have h1 := haD.2 (θ ^ n) (L.pow_mem hθL n)
      have e1 : a * θ ^ n * a⁻¹ * (θ ^ n)⁻¹ = (θ ^ n * a * (θ ^ n)⁻¹ * a⁻¹)⁻¹ := by group
      rw [e1]
      exact B.inv_mem h1

theorem relIndex_centralizer_th_or
    (hc : S.Coord θ e)
    {A : Subgroup G} (hVA : fsuV T I ≤ A)
    (hAQ : A ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G))
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hTA : T ≤ Subgroup.normalizer (A : Set G)) :
    (Subgroup.centralizer ({θ} : Set G)).relIndex A =
        (Subgroup.centralizer ({θ} : Set G)).relIndex (fsuV T I) ∨
      16 * (Subgroup.centralizer ({θ} : Set G)).relIndex (fsuV T I) ≤
        (Subgroup.centralizer ({θ} : Set G)).relIndex A := by
  classical
  induction h : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  by_cases hAV : A = fsuV T I
  · left
    rw [hAV]
  have hVlt : fsuV T I < A := lt_of_le_of_ne hVA (Ne.symm hAV)
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun X : Subgroup G => (X : Set G)) SetLike.coe_injective
  obtain ⟨B, ⟨hVB, hBA, hLB, hTB⟩, hBmax⟩ := wellFounded_gt.has_min
    {B : Subgroup G | fsuV T I ≤ B ∧ B < A ∧ L ≤ Subgroup.normalizer (B : Set G) ∧
      T ≤ Subgroup.normalizer (B : Set G)}
    ⟨fsuV T I, le_rfl, hVlt, S.L_le_normalizer_V, S.T_le_normalizer_V⟩
  have hirr : ∀ D : Subgroup G, B ≤ D → D ≤ A → L ⊔ T ≤ Subgroup.normalizer (D : Set G) →
      D = B ∨ D = A := by
    intro D hBD hDA hD
    by_contra hne
    push Not at hne
    exact hBmax D ⟨hVB.trans hBD, lt_of_le_of_ne hDA hne.2, le_sup_left.trans hD,
      le_sup_right.trans hD⟩ (lt_of_le_of_ne hBD (Ne.symm hne.1))
  have hB := ih (Nat.card B) (h ▸ Subgroup.card_lt_of_lt hBA) hVB (hBA.le.trans hAQ) hLB hTB rfl
  rcases relIndex_th_or_of_chief hc hBA hAQ hLA hTA hLB hTB hirr with h1 | h1
  · rw [h1]
    exact hB
  · right
    rcases hB with h2 | h2
    · rw [← h2]
      exact h1
    · calc 16 * (Subgroup.centralizer ({θ} : Set G)).relIndex (fsuV T I)
          ≤ (Subgroup.centralizer ({θ} : Set G)).relIndex B := h2
        _ ≤ 16 * (Subgroup.centralizer ({θ} : Set G)).relIndex B := Nat.le_mul_of_pos_left _
          (by norm_num)
        _ ≤ (Subgroup.centralizer ({θ} : Set G)).relIndex A := h1

end Setup

end CFSG.Quasithin.H13.Sec77
