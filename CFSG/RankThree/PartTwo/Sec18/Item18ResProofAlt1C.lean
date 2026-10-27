module

public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofStatements
public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofTools
public import CFSG.RankThree.PartTwo.Sec18.Item183KStatements
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemHc

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise commutatorElement

namespace Item18ResProof

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_map_conj_le {Y : Subgroup G} {g : G}
    (h : Y.map (MulAut.conj g).toMonoidHom ≤ Y) : g ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem mem_normalizer_of_commutator_mem {X Y : Subgroup G} (hY : Y ∈ oTwoComponentsIn X)
    {g : G} (hgX : g ∈ X)
    (hg : ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 X) :
    g ∈ Subgroup.normalizer (Y : Set G) := by
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  have hQg : Q.map (MulAut.conj g).toMonoidHom = Q :=
    Late.map_conj_eq_of_mem_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hgX)
  have hYg : Y.map (MulAut.conj g).toMonoidHom ≤ Y ⊔ Q := by
    rintro _ ⟨y, hy, rfl⟩
    have e : (MulAut.conj g).toMonoidHom y = (g * y * g⁻¹ * y⁻¹) * y := by
      simp [MulAut.conj_apply]
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup (hg y hy) hy
  have hsup : g ∈ Subgroup.normalizer ((Y ⊔ Q : Subgroup G) : Set G) := by
    refine mem_normalizer_of_map_conj_le ?_
    rw [Subgroup.map_sup, hQg]
    exact sup_le hYg le_sup_right
  have : (perfectResidual (Y ⊔ Q : Subgroup G)).Characteristic :=
    (CFSG.perfect_residual_characterization (G := (Y ⊔ Q : Subgroup G))).2.1
  have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (perfectResidual (Y ⊔ Q : Subgroup G)) hsup
  rwa [show (perfectResidual (Y ⊔ Q : Subgroup G)).map (Y ⊔ Q).subtype = Y from
    inSubgroup_perfectResidual_sup_pCoreOf hY] at h1

omit [Finite G] in
theorem map_conj_eq_of_pow_three {K J : Subgroup G} (hKJ : K ≠ J) {a : G} (ha : a ^ 3 = 1)
    (hK : K.map (MulAut.conj a).toMonoidHom = K ∨ K.map (MulAut.conj a).toMonoidHom = J)
    (hJ : J.map (MulAut.conj a).toMonoidHom = K ∨ J.map (MulAut.conj a).toMonoidHom = J) :
    K.map (MulAut.conj a).toMonoidHom = K := by
  have hmap : ∀ (U : Subgroup G) (b d : G), (U.map (MulAut.conj d).toMonoidHom).map
      (MulAut.conj b).toMonoidHom = U.map (MulAut.conj (b * d)).toMonoidHom := by
    intro U b d
    rw [Subgroup.map_map, map_mul]
    rfl
  rcases hK with h | h
  · exact h
  · exfalso
    rcases hJ with h' | h'
    ·
      have h3 : K.map (MulAut.conj (a * (a * a))).toMonoidHom = J := by
        rw [← hmap, ← hmap, h, h', h]
      have ha' : a * (a * a) = 1 := by rw [← ha, pow_three]
      have h1 : K.map (MulAut.conj (1 : G)).toMonoidHom = K :=
        Late.map_conj_eq_of_mem_normalizer (Subgroup.one_mem _)
      rw [ha', h1] at h3
      exact hKJ h3
    · apply hKJ
      have h2 : K.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj a).toMonoidHom := by
        rw [h, h']
      exact (Subgroup.map_injective (MulAut.conj a).injective) h2

omit [Finite G] in
theorem nonempty_quotient_map_conj {L : Subgroup G} (x : G) {Y : Type} [Group Y]
    (e : L ⧸ CFSG.pCore 2 L ≃* Y) :
    Nonempty (L.map (MulAut.conj x).toMonoidHom ⧸
      CFSG.pCore 2 (L.map (MulAut.conj x).toMonoidHom) ≃* Y) := by
  set f : L ≃* L.map (MulAut.conj x).toMonoidHom :=
    L.equivMapOfInjective _ (MulAut.conj x).injective
  exact ⟨(QuotientGroup.congr _ _ f (CFSG.pCore_map_iso 2 f)).symm.trans e⟩

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_mem_closure {K : Subgroup G} {S : Set G}
    (hS : ∀ s ∈ S, s ∈ Subgroup.normalizer (K : Set G) ∧
      ∀ k ∈ K, s * k * s⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K) {g : G}
    (hg : g ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  set Q := CFSG.Open.pCoreOf 2 K with hQ
  have hNQ : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  let T : Subgroup G :=
    { carrier := {w | w ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ Q}
      mul_mem' := by
        rintro w₁ w₂ ⟨hw₁, h₁⟩ ⟨hw₂, h₂⟩
        refine ⟨Subgroup.mul_mem _ hw₁ hw₂, fun k hk => ?_⟩
        have hk' : w₂ * k * w₂⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hw₂ k).mp hk
        have e : w₁ * w₂ * k * (w₁ * w₂)⁻¹ * k⁻¹ =
            (w₁ * (w₂ * k * w₂⁻¹) * w₁⁻¹ * (w₂ * k * w₂⁻¹)⁻¹) * (w₂ * k * w₂⁻¹ * k⁻¹) := by group
        rw [e]
        exact Q.mul_mem (h₁ _ hk') (h₂ k hk)
      one_mem' := ⟨Subgroup.one_mem _, fun k _ => by simp⟩
      inv_mem' := by
        rintro w ⟨hw, h⟩
        refine ⟨Subgroup.inv_mem _ hw, fun k hk => ?_⟩
        have hk' : w⁻¹ * k * w⁻¹⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw) k).mp hk
        have e : w⁻¹ * k * w⁻¹⁻¹ * k⁻¹ =
            (w * (w⁻¹ * k * w⁻¹⁻¹) * w⁻¹ * (w⁻¹ * k * w⁻¹⁻¹)⁻¹)⁻¹ := by group
        rw [e]
        exact Q.inv_mem (h _ hk') }
  have hle : Subgroup.closure S ≤ T := (Subgroup.closure_le T).mpr fun s hs => hS s hs
  exact hle hg

end Item18ResProof

open Item18ResProof in
theorem Item18ResProof.false_of_alt2
    (h1812 : Item181_2)
    (h183K : Item183K) {G : Type} [Group G] [Finite G] {A M : Subgroup G} (h : Sec18Std G A M)
    {H : Subgroup G} (hH : H ∈ scriptH A M) {X : Subgroup G} (hHX : H ≤ X) {K J : Subgroup G}
    (hK : K ∈ oTwoComponentsIn X) (hJ : J ∈ oTwoComponentsIn X) (hKM : ¬ K ≤ M)
    (eL : inSubgroup perfectResidual H ⧸ CFSG.pCore 2 (inSubgroup perfectResidual H) ≃*
      projSL 3 (GaloisField 2 2))
    (hLXeq : ⁅inSubgroup perfectResidual H, X⁆ = K ⊔ J)
    (eK : K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hCX : Subgroup.centralizer ({c} : Set G) ≤ X)
    (hcL : c ∈ sectionCentralizer A (inSubgroup perfectResidual H)
      (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := inSubgroup perfectResidual H with hLdef
  have hA := isE27_of_mem_partTwoE h.mem_partTwoE
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH : A ≤ H := le_of_mem_scriptH₀ hH₀
  have hAX : A ≤ X := hAH.trans hHX
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hLX : L ≤ X := hLH.trans hHX
  have hLp : ⁅L, L⁆ = L := commutator_inSubgroup_perfectResidual H
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_inSubgroup_perfectResidual H
  have hKX : K ≤ X := le_of_mem_oTwoComponentsIn hK
  have hJX : J ≤ X := le_of_mem_oTwoComponentsIn hJ
  set QX := CFSG.Open.pCoreOf 2 X with hQX
  set QK := CFSG.Open.pCoreOf 2 K with hQK
  have hXQX : X ≤ Subgroup.normalizer (QX : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hQKX : QK ≤ QX := pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK
  have hKQK : K ≤ Subgroup.normalizer (QK : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hKp : ⁅K, K⁆ = K := commutator_eq_of_mem_oTwoComponentsIn hK
  have hLKJ : L ≤ K ⊔ J := by
    rw [← hLXeq]
    calc L = ⁅L, L⁆ := hLp.symm
      _ ≤ ⁅L, X⁆ := Subgroup.commutator_mono le_rfl hLX
  have hKJne : K ≠ J := by
    rintro rfl
    rw [sup_idem] at hLKJ
    exact false_of_le_sup_pCoreOf hK eK eL (hLKJ.trans le_sup_left)
  have hJK : J ≤ Subgroup.normalizer (K : Set G) := fun j hj =>
    mem_normalizer_of_commutator_mem hK (hJX hj) fun k hk =>
      Sec19.Step1910Proof.commutator_mem_pCoreOf hJ hK (Ne.symm hKJne) hj hk
  have hKJ : K ≤ Subgroup.normalizer (J : Set G) := fun k hk =>
    mem_normalizer_of_commutator_mem hJ (hKX hk) fun j hj =>
      Sec19.Step1910Proof.commutator_mem_pCoreOf hK hJ hKJne hk hj
  have hQXK : QX ⊓ K ≤ QK := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hXQX (hKX hx), Subgroup.le_normalizer hx⟩)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_left)
  have hJKc : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ * k⁻¹ ∈ QK := fun j hj k hk =>
    hQXK ⟨Sec19.Step1910Proof.commutator_mem_pCoreOf hJ hK (Ne.symm hKJne) hj hk,
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hJK hj) k).mp hk) (K.inv_mem hk)⟩
  have hAKJ : ∀ a ∈ A, (K ⊔ J).map (MulAut.conj a).toMonoidHom = K ⊔ J := by
    intro a ha
    rw [← hLXeq, Subgroup.map_commutator, Late.map_conj_eq_of_mem_normalizer (hHL (hAH ha)),
      Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (hAX ha))]
  have hcomp : ∀ S ∈ oTwoComponentsIn X, S ≤ K ⊔ J → S = K ∨ S = J := by
    intro S hS hSKJ
    by_contra hne
    push Not at hne
    refine false_of_le_iSup_sup_pCoreOf hS {K, J} ?_ ?_ ?_
    · rintro T (rfl | rfl)
      · exact hK
      · exact hJ
    · rintro (h1 | h1)
      · exact hne.1 h1
      · exact hne.2 h1
    · refine hSKJ.trans (le_sup_of_le_left ?_)
      exact sup_le (le_iSup₂_of_le K (Set.mem_insert _ _) le_rfl)
        (le_iSup₂_of_le J (by simp) le_rfl)
  have hAnorm : ∀ a ∈ A, a ∈ Subgroup.normalizer (K : Set G) ∧
      a ∈ Subgroup.normalizer (J : Set G) := by
    intro a ha
    have hKa := hcomp _ (map_conj_mem_oTwoComponentsIn hK (hAX ha))
      (by rw [← hAKJ a ha]; exact Subgroup.map_mono le_sup_left)
    have hJa := hcomp _ (map_conj_mem_oTwoComponentsIn hJ (hAX ha))
      (by rw [← hAKJ a ha]; exact Subgroup.map_mono le_sup_right)
    have ha3 : a ^ 3 = 1 := hA.1.2 a ha
    exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_eq_of_pow_three hKJne ha3 hKa hJa),
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_eq_of_pow_three (Ne.symm hKJne) ha3 hJa.symm hKa.symm)⟩
  have hLJ : ¬ L ≤ J ⊔ QK := by
    intro hLJ'
    have hLJX : L ≤ J ⊔ QX := hLJ'.trans (sup_le_sup_left hQKX J)
    set 𝓢 : Set (Subgroup G) := {S | ∃ x ∈ X, S = J.map (MulAut.conj x).toMonoidHom} with h𝓢
    have h𝓢mem : ∀ S ∈ 𝓢, S ∈ oTwoComponentsIn X := by
      rintro S ⟨x, hx, rfl⟩
      exact map_conj_mem_oTwoComponentsIn hJ hx
    have hJ𝓢 : ∀ x ∈ X, J.map (MulAut.conj x).toMonoidHom ≤ ⨆ S ∈ 𝓢, S := fun x hx =>
      le_iSup₂_of_le (J.map (MulAut.conj x).toMonoidHom) ⟨x, hx, rfl⟩ le_rfl
    have hJ1 : J ≤ ⨆ S ∈ 𝓢, S :=
      le_iSup₂_of_le J
        ⟨1, X.one_mem, (Late.map_conj_eq_of_mem_normalizer (Subgroup.one_mem _)).symm⟩ le_rfl
    have hKle : K ≤ (⨆ S ∈ 𝓢, S) ⊔ QX := by
      have h1 : ⁅L, X⁆ ≤ (⨆ S ∈ 𝓢, S) ⊔ QX := by
        rw [Subgroup.commutator_le]
        intro l hl x hx
        have hl' : l ∈ ((J : Set G) * (QX : Set G)) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right J QX (hJX.trans hXQX)]
          exact hLJX hl
        obtain ⟨j, hj, q, hq, rfl⟩ := hl'
        have hjX : j ∈ X := hJX hj
        have hq1 : q * x * q⁻¹ * x⁻¹ ∈ QX := by
          have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
          rw [e]
          exact QX.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hXQX hx) _).mp (QX.inv_mem hq))
        have hq2 : j * (q * x * q⁻¹ * x⁻¹) * j⁻¹ ∈ QX :=
          (Subgroup.mem_normalizer_iff.mp (hXQX hjX) _).mp hq1
        have hj2 : x * j⁻¹ * x⁻¹ ∈ J.map (MulAut.conj x).toMonoidHom :=
          ⟨j⁻¹, J.inv_mem hj, by simp [MulAut.conj_apply]⟩
        have e : ⁅j * q, x⁆ = (j * (q * x * q⁻¹ * x⁻¹) * j⁻¹) * (j * (x * j⁻¹ * x⁻¹)) := by
          rw [commutatorElement_def]
          group
        rw [e]
        refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hq2) (Subgroup.mul_mem _ ?_ ?_)
        · exact Subgroup.mem_sup_left (hJ1 hj)
        · exact Subgroup.mem_sup_left (hJ𝓢 x hx hj2)
      exact (le_sup_left.trans hLXeq.symm.le).trans h1
    by_cases hK𝓢 : K ∈ 𝓢
    · obtain ⟨x, hx, hKx⟩ := hK𝓢
      have hLx : L.map (MulAut.conj x).toMonoidHom ≤ K ⊔ QX := by
        have h1 := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hLJX
        rwa [Subgroup.map_sup, ← hKx, Late.map_conj_eq_of_mem_normalizer (hXQX hx)] at h1
      obtain ⟨eLx⟩ := nonempty_quotient_map_conj x eL
      exact false_of_le_sup_pCoreOf hK eK eLx hLx
    · exact false_of_le_iSup_sup_pCoreOf hK 𝓢 h𝓢mem hK𝓢 hKle
  have hcK : c ∈ Subgroup.normalizer (K : Set G) := (hAnorm c hcA).1
  have hcJ : c ∈ Subgroup.normalizer (J : Set G) := (hAnorm c hcA).2
  have hcLc : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L := hcL.2
  have hcc : ∀ k ∈ K, c * k * c⁻¹ * k⁻¹ ∈ QK :=
    commutator_mem_pCoreOf_of_diag hJK hKJ hJKc hKp hLKJ hLp eK eL hLJ hcK hcJ hcLc
  have hc3 : c ^ 3 = 1 := hA.1.2 c hcA
  obtain ⟨hKcmem, ⟨eKc⟩, hKeq⟩ := mem_thetaComponentsAt_perfectResidual hK hCX hcK hc3 hcc
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set Kc := inSubgroup perfectResidual (K ⊓ C) with hKcdef
  have hKcK : Kc ≤ K := (Subgroup.map_subtype_le _).trans inf_le_left
  set Z := Subgroup.zpowers c with hZdef
  have hc3' : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hCZ : C ≤ Subgroup.normalizer (Z : Set G) := Rem187QProof.centralizer_le_normalizer_zpowers c
  obtain ⟨s, ⟨hsS, -, -, hsH, Xb, hXbn, hXb, hXbt, -⟩, -, -⟩ := h1812 G A M h H hH
  obtain ⟨h9, hcnL⟩ := Rem187QProof.card_inf_ge_and_not_mem h hH eL hsH hsS hXb hXbt hcA hc1 hcLc
  set Lc' := inSubgroup perfectResidual (H ⊓ C) with hLc'def
  have hLc'L : Lc' ≤ L := inSubgroup_perfectResidual_mono inf_le_left
  set B := A ⊓ Lc' with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBL : B ≤ L := inf_le_right.trans hLc'L
  have hBC : B ≤ C := hBA.trans hAC
  have hBZ : B ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    by_contra hb1
    have hb1' : b ≠ 1 := fun h => hb1 (Subgroup.mem_bot.mpr h)
    have hZb : (Z : Set G) = Subgroup.zpowers b :=
      Rem187QProof.coe_zpowers_eq_of_mem rfl hc3' hb.2 hb1'
    have hcb : c ∈ Subgroup.zpowers b := by
      rw [← SetLike.mem_coe, ← hZb]
      exact Subgroup.mem_zpowers c
    exact hcnL (hBL ((Subgroup.zpowers_le.mpr hb.1) hcb))
  have hABZ : A = B ⊔ Z := by
    have hle : B ⊔ Z ≤ A := sup_le hBA (Subgroup.zpowers_le.mpr hcA)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have h1 := Sec6.card_sup_mul_card_inf (X := B) (N := Z) (hBC.trans hCZ)
    rw [hBZ, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc3'] at h1
    have hBle : Nat.card B ≤ 27 := by
      rw [← hA.2]
      exact Subgroup.card_le_of_le hBA
    rw [h1, hA.2]
    omega
  have hinnerK : ∀ a ∈ A, ∃ k₀ ∈ K, ∀ y ∈ K, a * y * a⁻¹ * (k₀ * y * k₀⁻¹)⁻¹ ∈ QK := by
    intro a ha
    have haBZ : a ∈ ((B : Set G) * (Z : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right B Z (hBC.trans hCZ), ← hABZ]
      exact ha
    obtain ⟨b, hb, z, hz, rfl⟩ := haBZ
    have hbKJ : b ∈ ((K : Set G) * (J : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K J hJK]
      exact hLKJ (hBL hb)
    obtain ⟨k₀, hk₀, j₀, hj₀, rfl⟩ := hbKJ
    refine ⟨k₀, hk₀, fun y hy => ?_⟩
    have hS : ∀ t ∈ (J : Set G) ∪ {c}, t ∈ Subgroup.normalizer (K : Set G) ∧
        ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ QK := by
      rintro t (ht | ht)
      · exact ⟨hJK ht, hJKc t ht⟩
      · rw [Set.mem_singleton_iff] at ht
        subst ht
        exact ⟨hcK, hcc⟩
    have hjz : j₀ * z ∈ Subgroup.closure ((J : Set G) ∪ {c}) := by
      have hj' : j₀ ∈ Subgroup.closure ((J : Set G) ∪ {c}) :=
        Subgroup.subset_closure (Set.mem_union_left _ hj₀)
      have hc' : c ∈ Subgroup.closure ((J : Set G) ∪ {c}) :=
        Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton c))
      exact Subgroup.mul_mem _ hj' ((Subgroup.zpowers_le.mpr hc') hz)
    have ht := (commutator_mem_pCoreOf_of_mem_closure hS hjz).2 y hy
    have e : k₀ * j₀ * z * y * (k₀ * j₀ * z)⁻¹ * (k₀ * y * k₀⁻¹)⁻¹ =
        k₀ * (j₀ * z * y * (j₀ * z)⁻¹ * y⁻¹) * k₀⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKQK hk₀) _).mp ht
  have hQKKc : QK ⊓ Kc ≤ CFSG.Open.pCoreOf 2 Kc :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hKQK (hKcK hx), Subgroup.le_normalizer hx⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left)
  have hinner : ∀ a ∈ A, InducesInnerMod a Kc (CFSG.Open.pCoreOf 2 Kc) := by
    intro a ha
    have haKC : a ∈ Subgroup.normalizer ((K ⊓ C : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨(hAnorm a ha).1, Subgroup.le_normalizer (hAC ha)⟩
    have : (perfectResidual (K ⊓ C : Subgroup G)).Characteristic :=
      (CFSG.perfect_residual_characterization (G := (K ⊓ C : Subgroup G))).2.1
    have haKc : a ∈ Subgroup.normalizer (Kc : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (perfectResidual (K ⊓ C : Subgroup G)) haKC
    obtain ⟨k₀, hk₀, hk₀y⟩ := hinnerK a ha
    have hk₀' : k₀ ∈ ((Kc : Set G) * (QK : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Kc QK (hKcK.trans hKQK), ← hKeq]
      exact hk₀
    obtain ⟨kc, hkc, o, ho, rfl⟩ := hk₀'
    refine ⟨haKc, kc, hkc, fun y hy => ?_⟩
    have hyK : y ∈ K := hKcK hy
    have h1 := hk₀y y hyK
    have h2 : o * y * o⁻¹ * y⁻¹ ∈ QK := by
      have e : o * y * o⁻¹ * y⁻¹ = o * (y * o⁻¹ * y⁻¹) := by group
      rw [e]
      exact QK.mul_mem ho ((Subgroup.mem_normalizer_iff.mp (hKQK hyK) _).mp (QK.inv_mem ho))
    have h3 : kc * (o * y * o⁻¹ * y⁻¹) * kc⁻¹ ∈ QK :=
      (Subgroup.mem_normalizer_iff.mp (hKQK (hKcK hkc)) _).mp h2
    have e : a * y * a⁻¹ * (kc * y * kc⁻¹)⁻¹ =
        (a * y * a⁻¹ * (kc * o * y * (kc * o)⁻¹)⁻¹) * (kc * (o * y * o⁻¹ * y⁻¹) * kc⁻¹) := by
      group
    have hmemQ : a * y * a⁻¹ * (kc * y * kc⁻¹)⁻¹ ∈ QK := by
      rw [e]
      exact QK.mul_mem h1 h3
    have hmemKc : a * y * a⁻¹ * (kc * y * kc⁻¹)⁻¹ ∈ Kc :=
      Kc.mul_mem ((Subgroup.mem_normalizer_iff.mp haKc y).mp hy)
        (Kc.inv_mem (Kc.mul_mem (Kc.mul_mem hkc hy) (Kc.inv_mem hkc)))
    exact hQKKc ⟨hmemQ, hmemKc⟩
  have hKcM : Kc ≤ M := h183K G A M h c hcA hc1 Kc hKcmem ⟨eKc.trans eK⟩ hinner
  have hQKM : QK ≤ M := le_of_le_normalizer_of_isPGroup_two h
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    (fun a ha => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hAnorm a ha).1)
  exact hKM (hKeq.le.trans (sup_le hKcM hQKM))

theorem item182Alt1C_of
    (h4443 : Sec4.Item4_44_3)
    (h1812 : Item181_2) (h183K : Item183K) : Item182Alt1C := by
  intro G _ _ A M h H hH X hHX hX c hcA hc1 hCX hcL
  obtain ⟨K, hK, hKM, hcase⟩ :=
    Rem187Bypass.exists_mem_oTwoComponentsIn_of_item4443 h4443 h hH hHX hX
  rcases hcase with hi | ⟨⟨eL⟩, J, hJ, hLXeq, ⟨eK⟩, -⟩
  · exact ⟨K, hK, hi⟩
  · exact (Item18ResProof.false_of_alt2 h1812 h183K h hH hHX hK hJ hKM eL hLXeq eK hcA hc1
      hCX hcL).elim

end CFSG.RankThree.PartTwo.Sec18
