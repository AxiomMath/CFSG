module

public import CFSG.Quasithin.Vol2.Ch4Sec2Lem4212A
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace L4212

theorem le_oTwoUpper_of_perfect {X Y : Subgroup G} (hXY : X ≤ Y) (hX : ⁅X, X⁆ = X) :
    X ≤ oTwoUpper Y := calc
  X = oTwoUpper X := (C2Nine.oTwoUpper_eq_of_perfect hX).symm
  _ ≤ oTwoUpper Y := oTwoUpper_mono hXY

omit [Finite G] in
theorem oTwoUpper_sup_le {A P : Subgroup G} (hPA : P ≤ Subgroup.normalizer (A : Set G))
    (hP : IsPGroup 2 ↥P) : oTwoUpper (A ⊔ P) ≤ A := by
  refine oTwoUpper_le_of_pow_mem fun y hy => ?_
  rw [sup_comm] at hy
  obtain ⟨p, hp, a, ha, rfl⟩ := (mem_sup_of_le_normalizer hPA).mp hy
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨p, hp⟩
  refine ⟨k, ?_⟩
  have hpa : p * a * p⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hPA hp) a).mp ha
  obtain ⟨x', hx', he⟩ := A4.exists_pow_mul_eq hpa (hPA hp) (2 ^ k)
  have e : p * a = p * a * p⁻¹ * p := by group
  have hpk : p ^ 2 ^ k = 1 := by
    have := pow_orderOf_eq_one (⟨p, hp⟩ : ↥P)
    rw [hk] at this
    exact congrArg Subtype.val this
  rw [e, he, hpk, mul_one]
  exact hx'

theorem eq_of_isSubnormal_of_eq_sup {K Y P : Subgroup G} (hK : IsSubnormal K Y)
    (hP : IsPGroup 2 ↥P) (hYP : Y ≤ Subgroup.normalizer (P : Set G)) (hY : Y = K ⊔ P)
    (hYp : ⁅Y, Y⁆ = Y) : K = Y := by
  induction hK with
  | refl => rfl
  | @step K₁ M₁ Y hle hN hsub ih =>
    have hM₁Y : M₁ ≤ Y := A3.subnormal_le hsub
    have hPY : P ≤ Y := hY ▸ le_sup_right
    have hM₁ : M₁ = Y := ih hYP (le_antisymm (hY.trans_le (sup_le_sup_right hle P))
      (_root_.sup_le hM₁Y hPY)) hYp
    subst hM₁
    have hK₁n : M₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    have h1 : oTwoUpper M₁ ≤ K₁ := by
      have := oTwoUpper_sup_le (hPY.trans hK₁n) hP
      rwa [← hY] at this
    refine le_antisymm hle ?_
    calc M₁ = oTwoUpper M₁ := (C2Nine.oTwoUpper_eq_of_perfect hYp).symm
      _ ≤ K₁ := h1

theorem mem_cComp_of_le_sup {X X' L Y : Subgroup G} (hLc : L ∈ cComp X)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) (hYL : Y ≤ L) (hYp : ⁅Y, Y⁆ = Y)
    (hLY : L ≤ Y ⊔ pCoreOf 2 L) (hYsub : IsSubnormal Y X') : Y ∈ cComp X' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 L) := pCoreOf_isPGroup 2 L
  have hYO : Y ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hYL.trans (le_normalizer_pCoreOf 2 L)
  have hYne : Y ≠ ⊥ := by
    rintro rfl
    rw [bot_sup_eq] at hLY
    exact ne_bot_of_mem_cComp hLc (eq_bot_of_commutator_eq_self_of_isPGroup_two
      (perfect_of_mem_cComp hLc) (hO2.to_le hLY))
  refine ⟨hYne, hYp, hYsub, fun K hKY hKne hKp hKsub => ?_⟩
  have hKY' : IsSubnormal K Y := A3.subnormal_of_le_of_le hKsub hKY.le (A3.subnormal_le hYsub)
  have hmem : ∀ x : ↥L, (x : G) ∈ pCoreOf 2 L ↔ x ∈ CFSG.pCore 2 ↥L := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => by
      have : y = x := Subtype.ext hyx
      subst this
      assumption, fun hx => ⟨x, by assumption, rfl⟩⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hsubL : IsSubnormal (K.subgroupOf L) (Y.subgroupOf L) := A3.subnormal_comap L.subtype hKY'
  have hYtop : (Y.subgroupOf L).map π = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) z
    obtain ⟨y, hy, o, ho, rfl⟩ := (mem_sup_of_le_normalizer hYO).mp (hLY hl)
    have hyL : y ∈ L := hYL hy
    have hoL : o ∈ L := pCoreOf_le 2 L ho
    refine ⟨⟨y, hyL⟩, hy, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 : (⟨o, hoL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (hmem _).mp ho
    have e : (⟨y, hyL⟩ : ↥L)⁻¹ * ⟨y * o, Subgroup.mul_mem _ hyL hoL⟩ = ⟨o, hoL⟩ := by
      apply Subtype.ext
      simp
    rw [e]
    exact h1
  have hsubQ : IsSubnormal ((K.subgroupOf L).map π) ⊤ := by
    have := A3.subnormal_map π hsubL
    rwa [hYtop] at this
  rcases A3.eq_top_or_le_center_of_subnormal hq (A3.subnormal_top_iff.mp hsubQ) with htop | hcen
  ·
    have hLK : L ≤ K ⊔ pCoreOf 2 L := by
      intro l hl
      have hz : π ⟨l, hl⟩ ∈ (K.subgroupOf L).map π := htop ▸ Subgroup.mem_top _
      obtain ⟨⟨k, hkL⟩, hk, hke⟩ := hz
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hke
      have h1 : k⁻¹ * l ∈ pCoreOf 2 L := (hmem (⟨k, hkL⟩⁻¹ * ⟨l, hl⟩)).mpr hke
      have e : l = k * (k⁻¹ * l) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right h1)
    have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := hKY.le.trans hYO
    have hYeq : Y = K ⊔ (Y ⊓ pCoreOf 2 L) :=
      A3.eq_sup_inf_of_le_sup hKO hKY.le (hYL.trans hLK)
    have hYP : Y ≤ Subgroup.normalizer ((Y ⊓ pCoreOf 2 L : Subgroup G) : Set G) :=
      fun y hy => mem_normalizer_inf (Subgroup.le_normalizer hy) (hYO hy)
    exact hKY.ne (eq_of_isSubnormal_of_eq_sup hKY' (hO2.to_le inf_le_right) hYP hYeq hYp)
  ·
    have hKmap : ((K.subgroupOf L).map π) = ⊥ := by
      have hperf : ⁅(K.subgroupOf L).map π, (K.subgroupOf L).map π⁆ =
          (K.subgroupOf L).map π := by
        rw [← Subgroup.map_commutator]
        congr 1
        apply Subgroup.map_injective L.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hKY.le.trans hYL), hKp]
      rw [← hperf]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcen.trans (Subgroup.center_le_centralizer _))
    have hKO : K ≤ pCoreOf 2 L := by
      intro k hk
      have hkL : k ∈ L := (hKY.le.trans hYL) hk
      have h1 : π ⟨k, hkL⟩ ∈ (K.subgroupOf L).map π := ⟨⟨k, hkL⟩, hk, rfl⟩
      rw [hKmap, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact (hmem _).mpr h1
    exact hKne (eq_bot_of_commutator_eq_self_of_isPGroup_two hKp (hO2.to_le hKO))

theorem le_oTwoUpper_sup_pCoreOf {L B P : Subgroup G} (hLp : ⁅L, L⁆ = L) (hP : IsPGroup 2 ↥P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hLP : L ≤ Subgroup.normalizer (P : Set G))
    (hcov : ∀ l ∈ L, ∃ b ∈ B, ∃ q ∈ P, b * q = l) :
    oTwoUpper (B ⊓ (L ⊔ P)) ≤ B ⊓ L ∧ L ≤ oTwoUpper (B ⊓ (L ⊔ P)) ⊔ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := L ⊔ P with hY
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := _root_.sup_le hLP Subgroup.le_normalizer
  have h1 : L ≤ (B ⊓ Y) ⊔ P := by
    intro l hl
    obtain ⟨b, hb, q, hq, rfl⟩ := hcov l hl
    have hbY : b ∈ Y := by
      have e : b = b * q * q⁻¹ := by group
      rw [e]
      exact Y.mul_mem (Subgroup.mem_sup_left hl) (Y.inv_mem (Subgroup.mem_sup_right hq))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hb, hbY⟩) (Subgroup.mem_sup_right hq)
  have h2 : oTwoUpper Y ≤ oTwoUpper (Y ⊓ (B ⊓ Y)) ⊔ P :=
    oTwoUpper_le_sup_of_le_sup (_root_.sup_le h1 le_sup_right) (inf_le_right.trans hYP)
      le_sup_right
  rw [inf_eq_right.mpr inf_le_right] at h2
  have h3 : oTwoUpper Y ≤ L := oTwoUpper_sup_le hPL hP
  set J := oTwoUpper (B ⊓ Y) with hJ
  have hJL : J ≤ L := (oTwoUpper_mono inf_le_right).trans h3
  have hJB : J ≤ B := (oTwoUpper_le _).trans inf_le_left
  have h4 : L ≤ J ⊔ P := calc
    L = oTwoUpper L := (C2Nine.oTwoUpper_eq_of_perfect hLp).symm
    _ ≤ oTwoUpper Y := oTwoUpper_mono le_sup_left
    _ ≤ J ⊔ P := h2
  refine ⟨le_inf hJB hJL, ?_⟩
  have hJP : J ≤ Subgroup.normalizer (P : Set G) := hJL.trans hLP
  have h5 : L = J ⊔ (L ⊓ P) := A3.eq_sup_inf_of_le_sup hJP hJL h4
  have h6 : L ⊓ P ≤ pCoreOf 2 L :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun x hx => mem_normalizer_inf (Subgroup.le_normalizer hx) (hLP hx))
      (hP.to_le inf_le_right)
  rw [h5]
  exact sup_le_sup_left h6 _ |>.trans (sup_le_sup_left (le_of_eq (by rw [← h5])) _)

theorem le_of_perfect_of_le_sup {Y X W : Subgroup G} (hYp : ⁅Y, Y⁆ = Y) (hWY : W ≤ Y)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hXY : X ≤ Y) (hY : Y ≤ X ⊔ W)
    (hXW : perfectCore X ≤ W) : Y ≤ W := by
  set W' := W.subgroupOf Y with hW'
  have hW'n : W'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWY).mpr hYW
  set π := QuotientGroup.mk' W' with hπ
  set X' := X.subgroupOf Y with hX'
  have hXW' : X ≤ Subgroup.normalizer (W : Set G) := hXY.trans hYW
  have htop : X'.map π = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective W' z
    obtain ⟨x, hx, w, hw, rfl⟩ := (mem_sup_of_le_normalizer hXW').mp (hY hy)
    refine ⟨⟨x, hXY hx⟩, hx, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have e : (⟨x, hXY hx⟩ : ↥Y)⁻¹ * ⟨x * w, hy⟩ = ⟨w, hWY hw⟩ := by
      apply Subtype.ext
      simp
    rw [e]
    exact hw
  have hcore : perfectCore X' ≤ W' := by
    intro x hx
    have h1 : (x : G) ∈ (perfectCore X').map Y.subtype := ⟨x, hx, rfl⟩
    rw [map_perfectCore, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXY] at h1
    exact hXW h1
  have hQ : perfectCore (⊤ : Subgroup (↥Y ⧸ W')) = ⊥ := by
    rw [← htop, ← map_perfectCore, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hcore
  have hYtop : ⁅(⊤ : Subgroup ↥Y), (⊤ : Subgroup ↥Y)⁆ = (⊤ : Subgroup ↥Y) := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hYp
  have hQp : ⁅(⊤ : Subgroup (↥Y ⧸ W')), (⊤ : Subgroup (↥Y ⧸ W'))⁆ =
      (⊤ : Subgroup (↥Y ⧸ W')) := by
    have e : (⊤ : Subgroup (↥Y ⧸ W')) = (⊤ : Subgroup ↥Y).map π :=
      (Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective W')).symm
    rw [e, ← Subgroup.map_commutator, hYtop]
  rw [perfectCore_eq_self_of_perfect hQp] at hQ
  intro y hy
  have h1 : π ⟨y, hy⟩ ∈ (⊤ : Subgroup (↥Y ⧸ W')) := Subgroup.mem_top _
  rw [hQ, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end L4212

namespace Hyp4_2_3

variable {T M L Mm I : Subgroup G} (h : Hyp4_2_3 G T M L Mm I)
include h

theorem hyp4_1_1 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Hyp4_1_1 G T M (conjClosure L T) :=
  lemma_4_2_2 h37 h38 h39 h.toHyp4_2_1

theorem I_le : I ≤ M := h.gammaStar.1.1.1.trans h.sigma.1

theorem exists_conj_I (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {t : G}
    (ht : t ∈ T) : ∃ i ∈ I, CFSG.conjugate L t = CFSG.conjugate L i := by
  set Mp := conjClosure L T with hMp
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hC
  obtain ⟨m, hm, he⟩ := h.conjT t ht
  have hIota := h.gammaStar.1.1
  rw [← hIota.2.1] at hm
  have hMN : M ≤ Subgroup.normalizer (Mp : Set G) := h.le_normalizer_conjClosure h37 h38 h39
  have hIC : I ≤ Subgroup.normalizer (C : Set G) := fun i hi =>
    le_normalizer_centralizerSection M Mp ⟨h.I_le hi, hMN (h.I_le hi)⟩
  obtain ⟨i, hi, c, hc, rfl⟩ := (mem_sup_of_le_normalizer hIC).mp hm
  refine ⟨i, hi, he.trans (conjugate_mul_eq_of_mem_normalizer ?_)⟩
  exact h.centralizerSection_le_normalizer h37 h39
    ((Subgroup.mem_normalizer_iff.mp (hIC hi) c).mp hc)

theorem le_perfectCore_sup (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {H : Subgroup G} (hIH : I ≤ H) : L ≤ perfectCore (L ⊓ H) ⊔ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Mp := conjClosure L T with hMp
  set Q := pCoreOf 2 Mp with hQ
  have h41 := h.hyp4_1_1 h37 h38 h39
  obtain ⟨hMpeq, -⟩ := lemma_4_1_4_three h41 h.sigma h.gammaStar.1.1 hIH
  set Hp := oTwoUpper (Mp ⊓ H) with hHp
  have hMpN : Mp ≤ Subgroup.normalizer (L : Set G) :=
    conjClosure_le_normalizer_of_hyp421 h.toHyp4_2_1 h37 h39
  have hLMp : L ≤ Mp := le_conjClosure L T
  have hMpM : Mp ≤ M := h.toHyp4_2_1.conjClosure_le
  have hMN : M ≤ Subgroup.normalizer (Mp : Set G) := h.le_normalizer_conjClosure h37 h38 h39
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := (pCoreOf_le 2 Mp).trans hMpN
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := hLMp.trans (le_normalizer_pCoreOf 2 Mp)
  have hHpQ : Hp ≤ Subgroup.normalizer (Q : Set G) :=
    ((oTwoUpper_le _).trans (inf_le_left.trans hMpM)).trans
      (hMN.trans (normalizer_le_normalizer_pCoreOf 2 Mp))
  have hcov : ∀ l ∈ L, ∃ b ∈ Hp, ∃ q ∈ Q, b * q = l := fun l hl =>
    (mem_sup_of_le_normalizer hHpQ).mp (hMpeq ▸ hLMp hl)
  obtain ⟨hJ, hLJ⟩ :=
    L4212.le_oTwoUpper_sup_pCoreOf h.perfect (pCoreOf_isPGroup 2 Mp) hQN hLQ hcov
  have hJLH : oTwoUpper (Hp ⊓ (L ⊔ Q)) ≤ L ⊓ H :=
    le_inf (hJ.trans inf_le_right) (hJ.trans (inf_le_left.trans ((oTwoUpper_le _).trans
      inf_le_right)))
  have hL1 : L ≤ (L ⊓ H) ⊔ pCoreOf 2 L := hLJ.trans (sup_le_sup_right hJLH _)
  set W := perfectCore (L ⊓ H) ⊔ pCoreOf 2 L with hW
  have hLHO : L ⊓ H ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    inf_le_left.trans (le_normalizer_pCoreOf 2 L)
  have hcoreO : perfectCore (L ⊓ H) ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (perfectCore_le _).trans hLHO
  have hWN : L ≤ Subgroup.normalizer (W : Set G) := by
    intro l hl
    obtain ⟨a, ha, q, hq, rfl⟩ := (mem_sup_of_le_normalizer hLHO).mp (hL1 hl)
    refine Subgroup.mul_mem _ ?_ ?_
    ·
      have h1 : a ∈ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) :=
        normalizer_le_normalizer_perfectCore _ (Subgroup.le_normalizer ha)
      have h2 : a ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := hLHO ha
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
      rw [hW, Subgroup.map_sup, h1, h2]
    ·
      refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
      obtain ⟨x, hx, o, ho, rfl⟩ := (mem_sup_of_le_normalizer hcoreO).mp hw
      have hxL : x ∈ L := (perfectCore_le _).trans inf_le_left hx
      have hq1 : x⁻¹ * q * x * q⁻¹ ∈ pCoreOf 2 L := by
        have h1 : x⁻¹ * q * x ∈ pCoreOf 2 L := by
          have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (L.inv_mem hxL))
            q).mp hq
          simpa using this
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hq)
      have hq2 : q * o * q⁻¹ ∈ pCoreOf 2 L :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L
          ((pCoreOf_le 2 L) hq)) o).mp ho
      have e : q * (x * o) * q⁻¹ = x * ((x⁻¹ * q * x * q⁻¹) * (q * o * q⁻¹)) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
        (Subgroup.mem_sup_right (Subgroup.mul_mem _ hq1 hq2))
  exact L4212.le_of_perfect_of_le_sup h.perfect
    (_root_.sup_le ((perfectCore_le _).trans inf_le_left) (pCoreOf_le 2 L)) hWN inf_le_left
    (hL1.trans (sup_le_sup_left le_sup_right _)) le_sup_left

theorem mem_cComp_LH (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {H : Subgroup G} (hIH : I ≤ H) : perfectCore (L ⊓ H) ∈ cComp (H ⊓ M) := by
  have hLc : L ∈ cComp M := h.mem_cComp h37 h39
  have hsub : IsSubnormal (L ⊓ H) (H ⊓ M) := by
    have := A3.subnormal_inf_right (subnormal_of_mem_cComp hLc) (inf_le_right : H ⊓ M ≤ M)
    have e : L ⊓ (H ⊓ M) = L ⊓ H := by
      rw [inf_comm H M, ← inf_assoc, inf_eq_left.mpr h.L_le]
    rwa [e] at this
  exact L4212.mem_cComp_of_le_sup hLc h.quasisimple ((perfectCore_le _).trans inf_le_left)
    (perfectCore_perfect _) (h.le_perfectCore_sup h37 h38 h39 hIH) (A3.subnormal_perfectCore hsub)

theorem conjClosure_LH_eq (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {H : Subgroup G} (hIH : I ≤ H) :
    conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = oTwoUpper (conjClosure L T ⊓ H) := by
  set Mp := conjClosure L T with hMp
  set Q := pCoreOf 2 Mp with hQ
  set LH := perfectCore (L ⊓ H) with hLH
  set M0 := conjClosure LH (H ⊓ M) with hM0
  have hLMp : L ≤ Mp := le_conjClosure L T
  have hMN : M ≤ Subgroup.normalizer (Mp : Set G) := h.le_normalizer_conjClosure h37 h38 h39
  have hLHp : ⁅LH, LH⁆ = LH := perfectCore_perfect _
  have hLHL : LH ≤ L := (perfectCore_le _).trans inf_le_left
  have hLHH : LH ≤ H := (perfectCore_le _).trans inf_le_right
  have hM0H : M0 ≤ H := CFSG.Quasithin.conjClosure_le fun g hg x hx =>
    H.mul_mem (H.mul_mem hg.1 (hLHH hx)) (H.inv_mem hg.1)
  have hM0M : M0 ≤ M := CFSG.Quasithin.conjClosure_le fun g hg x hx =>
    M.mul_mem (M.mul_mem hg.2 (h.L_le (hLHL hx))) (M.inv_mem hg.2)
  apply le_antisymm
  ·
    refine CFSG.Quasithin.conjClosure_le fun g hg x hx => ?_
    have hle : LH.map (MulAut.conj g).toMonoidHom ≤ Mp ⊓ H := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMN hg.2) y).mp (hLMp (hLHL hy)), ?_⟩
      exact H.mul_mem (H.mul_mem hg.1 (hLHH hy)) (H.inv_mem hg.1)
    have hperf : ⁅LH.map (MulAut.conj g).toMonoidHom, LH.map (MulAut.conj g).toMonoidHom⁆ =
        LH.map (MulAut.conj g).toMonoidHom := by
      rw [← Subgroup.map_commutator, hLHp]
    exact L4212.le_oTwoUpper_of_perfect hle hperf ⟨x, hx, rfl⟩
  ·
    have hO2 : pCoreOf 2 L ≤ Q := h.pCoreOf_le_pCoreOf_conjClosure h37 h39
    have hLHO : LH ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      hLHL.trans (le_normalizer_pCoreOf 2 L)
    have hMp0 : Mp ≤ M0 ⊔ Q := by
      refine CFSG.Quasithin.conjClosure_le fun t ht l hl => ?_
      obtain ⟨i, hi, hti⟩ := h.exists_conj_I h37 h38 h39 (T.inv_mem ht)
      have hmem : t * l * t⁻¹ ∈ CFSG.conjugate L t⁻¹ := by
        refine ⟨l, hl, ?_⟩
        simp [MulAut.conj_apply]
      rw [hti] at hmem
      obtain ⟨l', hl', hl'e⟩ := hmem
      replace hl'e : i⁻¹ * l' * i = t * l * t⁻¹ := by simpa [MulAut.conj_apply] using hl'e
      obtain ⟨a, ha, o, ho, rfl⟩ :=
        (mem_sup_of_le_normalizer hLHO).mp (h.le_perfectCore_sup h37 h38 h39 hIH hl')
      have hiHM : i⁻¹ ∈ H ⊓ M := ⟨H.inv_mem (hIH hi), M.inv_mem (h.I_le hi)⟩
      have haM0 : i⁻¹ * a * i ∈ M0 := by
        have := mem_conjClosure hiHM ha
        simpa using this
      have hoQ : i⁻¹ * o * i ∈ Q := by
        have := (Subgroup.mem_normalizer_iff.mp ((normalizer_le_normalizer_pCoreOf 2 Mp)
          (hMN hiHM.2)) o).mp (hO2 ho)
        simpa using this
      rw [← hl'e]
      have e : i⁻¹ * (a * o) * i = (i⁻¹ * a * i) * (i⁻¹ * o * i) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haM0) (Subgroup.mem_sup_right hoQ)
    have hM0Q : M0 ≤ Subgroup.normalizer (Q : Set G) :=
      hM0M.trans (hMN.trans (normalizer_le_normalizer_pCoreOf 2 Mp))
    have h1 : Mp ⊓ H ≤ M0 ⊔ (Q ⊓ H) := by
      rintro y ⟨hyMp, hyH⟩
      obtain ⟨a, ha, q, hq, rfl⟩ := (mem_sup_of_le_normalizer hM0Q).mp (hMp0 hyMp)
      have hqH : q ∈ H := by
        have := H.mul_mem (H.inv_mem (hM0H ha)) hyH
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ⟨hq, hqH⟩)
    have hQHN : Q ⊓ H ≤ Subgroup.normalizer (M0 : Set G) := fun q hq =>
      le_normalizer_conjClosure LH (H ⊓ M) ⟨hq.2, (pCoreOf_le 2 Mp).trans
        h.toHyp4_2_1.conjClosure_le hq.1⟩
    exact (oTwoUpper_mono h1).trans
      (L4212.oTwoUpper_sup_le hQHN ((pCoreOf_isPGroup 2 Mp).to_le inf_le_left))

theorem conjClosure_perfect :
    ⁅conjClosure L T, conjClosure L T⁆ = conjClosure L T := by
  refine le_antisymm (A3.commutator_self_le _) (CFSG.Quasithin.conjClosure_le fun t ht l hl => ?_)
  have hperf : ⁅L.map (MulAut.conj t).toMonoidHom, L.map (MulAut.conj t).toMonoidHom⁆ =
      L.map (MulAut.conj t).toMonoidHom := by
    rw [← Subgroup.map_commutator, h.perfect]
  have hle : L.map (MulAut.conj t).toMonoidHom ≤ conjClosure L T := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_conjClosure ht hy
  have hmem : t * l * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := ⟨l, hl, rfl⟩
  rw [← hperf] at hmem
  exact Subgroup.commutator_mono hle hle hmem

theorem pCoreOf_sup_eq_inf :
    pCoreOf 2 (L ⊔ T) =
      T ⊓ centralizerSection M (conjClosure L T) (pCoreOf 2 (conjClosure L T)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Mp := conjClosure L T with hMp
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hC
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_le h.sylow le_sup_right
  have hTMp : T ≤ Subgroup.normalizer (Mp : Set G) := CFSG.Quasithin.le_normalizer_conjClosure L T
  have hO2T : pCoreOf 2 Mp ≤ T := by
    have hTsyl' : IsSylowTwoOf T (Mp ⊔ T) := isSylowTwoOf_of_le h.sylow le_sup_right
    refine (le_of_normal_of_isSylowTwoOf hTsyl' ((pCoreOf_le 2 Mp).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 Mp))
    refine Subgroup.normal_subgroupOf_of_le_normalizer ((_root_.sup_le Subgroup.le_normalizer
      hTMp).trans (normalizer_le_normalizer_pCoreOf 2 Mp))
  apply le_antisymm
  · exact le_inf (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
      h.toHyp4_2_1.pCoreOf_sup_le_centralizerSection
  · refine le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) (_root_.sup_le ?_ ?_)
      (h.sylow.1.to_le inf_le_left)
    · intro l hl
      refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
      have hc : l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 Mp :=
        (mem_centralizerSection.mp hx.2).2.2.2 l (le_conjClosure L T hl)
      have e : l * x * l⁻¹ = (l * x * l⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact (T ⊓ C).mul_mem ⟨hO2T hc, pCoreOf_le_centralizerSection
        h.toHyp4_2_1.conjClosure_le hc⟩ hx
    · intro t ht
      exact mem_normalizer_inf (Subgroup.le_normalizer ht)
        (le_normalizer_centralizerSection M Mp ⟨h.T_le ht, hTMp ht⟩)

theorem V_ne_bot (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK) :
    ⁅omegaOneCenterOf (T ⊓ centralizerSection M (conjClosure L T)
      (pCoreOf 2 (conjClosure L T))), conjClosure L T⁆ ≠ ⊥ := by
  have hT := lemma_1_2_10_of_maximal h.qtke h.simple h.nonabelian h36 h37 h39 h.sylow h.maximal
    (H := L ⊔ T) ⟨le_rfl, h.maximal.1.2.2.2⟩
  have h3 : ⁅twoReducedJoin (L ⊔ T), L⁆ ≠ ⊥ := (hT.out 1 3).mp h.faithful
  intro h0
  apply h3
  refine le_bot_iff.mp (h0 ▸ Subgroup.commutator_mono ?_ (le_conjClosure L T))
  rw [← h.pCoreOf_sup_eq_inf]
  exact Hyp4_2_1.twoReducedJoin_le_omegaOneCenterOf _

theorem lemma_4_2_4 (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {H : Subgroup G} (hH : InH I H) (hHM : ¬ H ≤ M) :
    HypC28 H (pCoreOf 2 I) (H ⊓ M) (perfectCore (L ⊓ H))
      ⁅omegaOneCenterOf (T ⊓ centralizerSection M (conjClosure L T)
        (pCoreOf 2 (conjClosure L T))), conjClosure L T⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Mp := conjClosure L T with hMp
  set C := centralizerSection M Mp (pCoreOf 2 Mp) with hC
  set Rp := T ⊓ C with hRpdef
  set R := pCoreOf 2 I with hRdef
  set V := ⁅omegaOneCenterOf Rp, Mp⁆ with hVdef
  set Hp := oTwoUpper (Mp ⊓ H) with hHp
  have h41 := h.hyp4_1_1 h37 h38 h39
  have hS := h.sigma
  have hI := h.gammaStar
  have hIH : I ≤ H := hH.1
  have hM0 : conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = Hp := h.conjClosure_LH_eq h37 h38 h39 hIH
  have hsyl : IsSylowTwoOf R (centralizerSection (H ⊓ M) Hp (pCoreOf 2 Hp)) :=
    (lemma_4_1_4_four h41 hS hI hH hHM).2
  have hRp : IsSylowTwoOf Rp C :=
    isSylowTwoOf_inf_centralizerSection (isSylowTwoOf_of_le h.sylow
      (le_inf h.T_le (CFSG.Quasithin.le_normalizer_conjClosure L T)))
  have hRpN : Mp ≤ Subgroup.normalizer (Rp : Set G) := by
    rw [hRpdef, ← h.pCoreOf_sup_eq_inf]
    have hMpLT : Mp ≤ L ⊔ T := CFSG.Quasithin.conjClosure_le fun t ht l hl =>
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer
        (Subgroup.mem_sup_right ht : t ∈ L ⊔ T)) l).mp (Subgroup.mem_sup_left hl)
    exact hMpLT.trans (le_normalizer_pCoreOf 2 _)
  have hVle : V ≤ omegaOneCenterOf Rp :=
    commutator_le_left_of_le_normalizer (hRpN.trans (normalizer_le_normalizer_omegaOneCenterOf _))
  have hVne : V ≠ ⊥ := h.V_ne_bot h36 h37 h39
  have hΩMp : omegaOneCenterOf Rp ≤ Subgroup.normalizer (Mp : Set G) :=
    (omegaOneCenterOf_le _).trans (inf_le_left.trans (CFSG.Quasithin.le_normalizer_conjClosure L T))
  have hVeq : V = ⁅V, Mp⁆ :=
    commutator_eq_commutator_commutator_of_perfect h.conjClosure_perfect hΩMp
      (hRpN.trans (normalizer_le_normalizer_omegaOneCenterOf _))
  have hRRp : R ≤ Rp := h.R_le
  have hVR : V ≤ centerOf R := lemma_4_1_5_one h41 hS hRp hVle hI hRRp
  have hVN : Subgroup.normalizer (V : Set G) ≤ M := lemma_4_1_5_two h41 hRp hVne hVle rfl
  have hVHp : V = ⁅V, Hp⁆ := lemma_4_1_5_three h41 hS hRp hVeq hVle hI.1.1 hIH
  have hRHM : R ≤ H ⊓ M := hsyl.1.trans (centralizerSection_le_left _ _ _)
  have hHpN : H ⊓ M ≤ Subgroup.normalizer (Hp : Set G) :=
    (lemma_4_1_4_three h41 hS hI.1.1 hIH).2
  have hHpHM : Hp ≤ H ⊓ M := le_inf ((oTwoUpper_le _).trans inf_le_right)
    ((oTwoUpper_le _).trans (inf_le_left.trans h.toHyp4_2_1.conjClosure_le))
  have hVRle : V ≤ R := (inf_le_left : centerOf R ≤ R).trans' hVR
  have hVle0 : V ≤ Hp := by
    rw [hVHp]
    exact commutator_le_right_of_le_normalizer (hVRle.trans (hRHM.trans hHpN))
  have hO2HpR : pCoreOf 2 (Hp ⊔ R) ≤ R := by
    set P := pCoreOf 2 (Hp ⊔ R) with hP
    have hHpRHM : Hp ⊔ R ≤ H ⊓ M := _root_.sup_le hHpHM hRHM
    have hPC : P ≤ centralizerSection (H ⊓ M) Hp (pCoreOf 2 Hp) := by
      refine (le_centralizerSection_iff (pCoreOf_le 2 Hp)).mpr
        ⟨(pCoreOf_le 2 _).trans hHpRHM, ?_⟩
      have hc1 : ⁅Hp, P⁆ ≤ Hp := Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((pCoreOf_le 2 _).trans (hHpRHM.trans hHpN))
      have hc2 : ⁅Hp, P⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_right.mp
        (le_sup_left.trans (le_normalizer_pCoreOf 2 _))
      refine (le_inf hc1 hc2).trans (le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right))
      exact fun x hx => mem_normalizer_inf (Subgroup.le_normalizer hx)
        (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hx))
    have hPR2 : IsPGroup 2 ↥(P ⊔ R) :=
      IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 _) (pCoreOf_isPGroup 2 I)
        (le_sup_right.trans (le_normalizer_pCoreOf 2 _))
    have hle := (isSylowTwoOf_iff_maximal.mp hsyl).2.2 (P ⊔ R) (_root_.sup_le hPC hsyl.1) hPR2
      le_sup_right
    exact le_sup_left.trans hle
  have hVO : V ≤ pCoreOf 2 (Hp ⊔ R) := by
    have hRV : R ≤ Subgroup.normalizer (V : Set G) := fun r hr =>
      mem_normalizer_commutator ((normalizer_le_normalizer_omegaOneCenterOf Rp)
        (Subgroup.le_normalizer (hRRp hr))) ((CFSG.Quasithin.le_normalizer_conjClosure L T)
          ((inf_le_left : Rp ≤ T) (hRRp hr)))
    have hHpV : Hp ≤ Subgroup.normalizer (V : Set G) := by
      rw [hVHp]
      exact Subgroup.normalizer_commutator_ge_right _ _
    refine le_pCoreOf_of_le_normalizer 2 (hVle0.trans le_sup_left) (_root_.sup_le ?_ hRV)
      (h.sylow.1.to_le (hVle.trans ((omegaOneCenterOf_le Rp).trans inf_le_left)))
    exact hHpV
  refine
    { sqtk := sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hH.2
      pgroup := pCoreOf_isPGroup 2 I
      le_M := hRHM
      le_H := inf_le_left
      charTwo := lemma_4_1_4_six h41 hS hI hH hHM
      pCore_ne := hH.2
      comp := h.mem_cComp_LH h37 h38 h39 hIH
      sylow := by rw [hM0]; exact hsyl
      cgs := cgsIn_le_inf_of_CGS_le (lemma_4_1_4_two h41 hS hI)
      V_le := by rw [hM0]; exact hVle0
      V_ne := hVne
      V_elem := isElemAbelian_of_le_omegaOneCenterOf hVle
      V_comm := by rw [hM0]; exact hVHp.symm
      V_center := by
        rw [hM0]
        exact le_inf hVO (le_centralizer_of_le_omegaOneCenterOf hVle (hO2HpR.trans hRRp))
      V_norm := le_inf inf_le_left (inf_le_right.trans hVN) }

end Hyp4_2_3

end CFSG.Quasithin.H13.Ch4
