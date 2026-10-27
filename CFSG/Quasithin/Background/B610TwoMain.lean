module

public import CFSG.Quasithin.Background.B610TwoGen
public import CFSG.Quasithin.H13.GoldschmidtC137DE
public import CFSG.Quasithin.H13.GoldschmidtC137BaumMain
public import CFSG.Quasithin.Background.C124L2MP
public import CFSG.Quasithin.Background.B610Two

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.U3
open scoped Pointwise

variable {G : Type} [Group G]

theorem hDE_of_offender [Finite G] {X L R V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hLX : L ≤ X) (hRX : R ≤ X) (hR : IsPGroup 2 R)
    (hA₂ : IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
      ((L ⊔ R) ⊓ Subgroup.centralizer (V : Set G)))
    {A₀ : Subgroup G} (hA₀ : IsMaxElemAbelian R A₀) {ℓ : G} (hℓ : ℓ ∈ L)
    (hgen : autI hV L ≤ autI hV A₀ ⊔ B1.conjAut (convI hV ⟨ℓ, hXN (hLX hℓ)⟩) (autI hV A₀))
    (hsum : 2 * rkIdx (fixV (autI hV A₀)) ≤ rkIdx (fixV (autI hV L)))
    (hoff : ∀ A, IsFFStarOffender (autI hV R) A → A ≤ autI hV A₀) :
    ∃ (n : ℕ) (Y : Fin n → Subgroup (MulAut (IntMod V hV))) (Rs : Fin n → Subgroup G),
      (∀ i, ∃ g ∈ autI hV L, B1.conjAut g (Y i) ≤ autI hV R) ∧
      (∀ i, Rs i ≤ X ∧ IsSylowTwoOf (Rs i) (GC137.starPreIn hV (L ⊔ R) (Y i))) ∧
      (∀ i, Y i = autI hV (thompsonJ (Rs i))) ∧
      (∀ i, CFSG.Open.pRank 2 (Rs i) = CFSG.Open.pRank 2 R) ∧
      autI hV L ≤ ⨆ i, Y i ∧ ∑ i, rkIdx (fixV (Y i)) ≤ rkIdx (fixV (autI hV L)) ∧
      ∀ A, IsFFStarOffender (autI hV R) A →
        ∃ (r : ℕ) (Ai : Fin r → Subgroup (MulAut (IntMod V hV))), A = ⨆ k, Ai k ∧
          ∀ k, IsFFStarOffender (autI hV R) (Ai k) ∧ ∃ j : Fin n, ∃ g ∈ autI hV L,
            Ai k ≤ B1.conjAut g (Y j) ∧ B1.conjAut g (Y j) ≤ autI hV R := by
  set ℓs : Fin 2 → G := ![1, ℓ] with hℓs
  have hℓsL : ∀ i, ℓs i ∈ L := Fin.forall_fin_two.mpr ⟨L.one_mem, hℓ⟩
  set c : Fin 2 → MulAut (IntMod V hV) := fun i => convI hV ⟨ℓs i, hXN (hLX (hℓsL i))⟩ with hc
  have hc0 : c 0 = 1 := by
    show convI hV (1 : ↥(Subgroup.normalizer (V : Set G))) = 1
    exact map_one _
  have hcL : ∀ i, c i ∈ autI hV L := fun i => convI_mem_autI hV (hℓsL i) _
  have hpieces := fun i => GC137.exists_Dpiece hV hXN hLX hRX hR hA₂ hA₀ (hℓsL i)
  have hY0 : B1.conjAut (c 0) (autI hV A₀) = autI hV A₀ := by
    rw [hc0, GC137.conjAut_one_gc]
  refine ⟨2, fun i => B1.conjAut (c i) (autI hV A₀),
    fun i => cjSub (ℓs i) (GC137.starPreIn hV R (autI hV A₀)), fun i => ?_, fun i => ?_,
    fun i => ?_, fun i => ?_, ?_, ?_, ?_⟩
  · refine ⟨(c i)⁻¹, Subgroup.inv_mem _ (hcL i), ?_⟩
    show B1.conjAut (c i)⁻¹ (B1.conjAut (c i) (autI hV A₀)) ≤ autI hV R
    rw [B1.conjAut_inv_conjAut]
    exact autI_mono hV hA₀.1
  · exact ⟨(hpieces i).1, (hpieces i).2.1⟩
  · exact (hpieces i).2.2.1
  · exact (hpieces i).2.2.2
  · refine hgen.trans (sup_le ?_ ?_)
    · exact le_iSup_of_le (f := fun i => B1.conjAut (c i) (autI hV A₀)) (0 : Fin 2) hY0.ge
    · exact le_iSup_of_le (f := fun i => B1.conjAut (c i) (autI hV A₀)) (1 : Fin 2) le_rfl
  · simp only [Fin.sum_univ_two, GC137.rkIdx_fixV_conjAut]
    omega
  · intro A hA
    refine ⟨1, fun _ => A, iSup_const.symm, fun _ => ⟨hA, 0, 1, (autI hV L).one_mem, ?_, ?_⟩⟩
    · show A ≤ B1.conjAut 1 (B1.conjAut (c 0) (autI hV A₀))
      rw [GC137.conjAut_one_gc, hY0]
      exact hoff A hA
    · show B1.conjAut 1 (B1.conjAut (c 0) (autI hV A₀)) ≤ autI hV R
      rw [GC137.conjAut_one_gc, hY0]
      exact autI_mono hV hA₀.1

theorem b610Two_holds : B610Two := by
  intro G _ _ X T M V L n hMP _ hred hLX hXNL hXLT hO2 hCL hn hnat hJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hFc, ⟨D⟩⟩ := exists_natData hn hnat
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hFc]
  have : CharP F 2 := charP_of_card_eq_prime_pow hFc
  have hn1 : 1 ≤ n := by omega
  have hVX : V ≤ X := hred.1
  have hXV : X ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hV : IsElemAbelian 2 V := hred.2.2.1
  have hTX : T ≤ X := hMP.isSylow.1
  have hT2 : IsPGroup 2 T := hMP.isSylow.2.1
  have hXN : X ≤ nLV L V := fun x hx => ⟨hXNL hx, hXV hx⟩
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hLX.trans hXV
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hTX.trans hXV
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hTX.trans hXNL
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    IntMod.val_comm (hV := hV) ⟨a, ha⟩ ⟨b, hb⟩
  have hsq : ∀ v : IntMod V hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one (hV := hV) v
  have hfaith : ∀ g : ↥(nLV L V), (g : G) ∈ X → D.act g = 1 →
      (g : G) ∈ Subgroup.centralizer (V : Set G) :=
    fun g hgX hg => D.act_faithful hred hT2 hXLT hXN g hgX hg
  have hVT : V ≤ T := A4.le_of_normal_of_isSylowTwoOf hMP.isSylow hVX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hVX).mpr hXV) (B2F.isPGroup_of_isElemAbelian hV)
  have hpowL : ∀ x ∈ X, ∃ a : ℕ, x ^ 2 ^ a ∈ L := by
    intro x hx
    have hxLT : x ∈ ((L : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTL, ← hXLT]
      exact hx
    obtain ⟨l, hl, t, ht, rfl⟩ := hxLT
    obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := pow_mul_eq hl (hTL ht) (2 ^ a)
    rw [hta, mul_one] at he
    exact ⟨a, he ▸ hl'⟩
  have hLodd : L = Setup.oddOrderSubgroup X := by
    apply le_antisymm
    · have hNL : L ⊓ Setup.oddOrderSubgroup X ≤ L := inf_le_left
      have hNn : ((L ⊓ Setup.oddOrderSubgroup X).subgroupOf L).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNL]
        intro l hl
        have hlO : l ∈ Subgroup.normalizer (Setup.oddOrderSubgroup X : Set G) :=
          Setup.normalizer_le_normalizer_oddOrderSubgroup X (Subgroup.le_normalizer (hLX hl))
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨hy1, hy2⟩
          exact ⟨L.mul_mem (L.mul_mem hl hy1) (L.inv_mem hl),
            (Subgroup.mem_normalizer_iff.mp hlO y).mp hy2⟩
        · rintro ⟨hy1, hy2⟩
          refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hlO y).mpr hy2⟩
          have := L.mul_mem (L.mul_mem (L.inv_mem hl) hy1) hl
          simpa [mul_assoc] using this
      have hNpow : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ L ⊓ Setup.oddOrderSubgroup X := by
        intro x hx
        obtain ⟨k, hk⟩ := Setup.exists_pow_mem_oddOrderSubgroup (hLX hx)
        exact ⟨k, L.pow_mem hx _, hk⟩
      have hNeq := hO2 _ hNL hNn hNpow
      calc L = L ⊓ Setup.oddOrderSubgroup X := hNeq.symm
        _ ≤ Setup.oddOrderSubgroup X := inf_le_right
    · exact Setup.oddOrderSubgroup_le_of_pow_mem hpowL
  have hO2p : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hCV2 : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G)) := by
    intro x
    obtain ⟨a, ha⟩ := hpowL x x.2.1
    have hxa : (x : G) ^ 2 ^ a ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨ha, Subgroup.pow_mem _ x.2.2 _⟩
    obtain ⟨b, hb⟩ := hO2p ⟨_, hCL hxa⟩
    have hb' : ((x : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    refine ⟨a + b, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul, hb']
  have hXnC : X ≤ Subgroup.normalizer
      ((X ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro h hh
    have hhC : h ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
      B2F.normalizer_le_normalizer_centralizer V (hXV hh)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨X.mul_mem (X.mul_mem hh hy1) (X.inv_mem hh),
        (Subgroup.mem_normalizer_iff.mp hhC y).mp hy2⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hhC y).mpr hy2⟩
      have := X.mul_mem (X.mul_mem (X.inv_mem hh) hy1) hh
      simpa [mul_assoc] using this
  have hCV : X ⊓ Subgroup.centralizer (V : Set G) ≤ T :=
    A4.le_of_normal_of_isSylowTwoOf hMP.isSylow inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hXnC) hCV2
  have hOL : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hOC : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    hred.2.2.2 _ (hOL.trans hLX)
      (hXNL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)) fun d hd => by
        obtain ⟨k, hk⟩ := hO2p ⟨d, hd⟩
        have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        refine ⟨k, ?_⟩
        rw [hk']
        exact Subgroup.one_mem _
  have hA₁ : pCoreOf 2 L ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf (fun x hx => hCV ⟨hLX (hOL hx), hOC hx⟩) hOC
  have hTC : T ⊓ Subgroup.centralizer (V : Set G) = X ⊓ Subgroup.centralizer (V : Set G) :=
    le_antisymm (inf_le_inf_right _ hTX) (le_inf hCV inf_le_right)
  have hA₂ : IsSylowTwoOf (T ⊓ Subgroup.centralizer (V : Set G))
      ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    rw [← hXLT, hTC]
    refine ⟨le_rfl, hCV2, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num
  have hA₃ : L ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [hTC]
    exact hLX.trans hXnC
  have hB : (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf X ≤ oTwoPhi (L.subgroupOf X) := by
    have hPO : pCoreOf 2 (L.subgroupOf X) ≤ oTwoPhi (L.subgroupOf X) := by
      unfold pCoreOf oTwoPhi
      refine Subgroup.map_mono fun y hy => ?_
      rw [Subgroup.mem_comap]
      have : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(L.subgroupOf X)) y = 1 :=
        (QuotientGroup.eq_one_iff y).2 hy
      rw [this]
      exact Subgroup.one_mem _
    intro x hx
    refine hPO ?_
    rw [GC137.pCoreOf_subgroupOf_eq hLX]
    exact hCL (Subgroup.mem_subgroupOf.mp hx)
  have hoffV : ∀ {B : Subgroup (MulAut (IntMod V hV))}, IsFFStarOffender (autI hV T) B →
      Nat.card (IntMod V hV) ≤ Nat.card B * Nat.card (fixV B) := by
    intro B hB'
    have := hB'.2.2.2 ⊥ bot_le
    rwa [B1.card_bot_mul_card_fixV] at this
  have hcore : ∀ {B : Subgroup (MulAut (IntMod V hV))}, IsFFStarOffender (autI hV T) B →
      B ≤ autI hV L ∧ Nat.card B = 2 ^ n ∧
        2 ^ n * Nat.card (fixV B) ≤ Nat.card (IntMod V hV) := fun hB' =>
    D.offender_core hn1 hF hV hLX hXN hfaith (hB'.1.trans (autI_mono hV hTX)) hB'.2.1
      hB'.2.2.1 (hoffV hB')
  have hC : ∀ B, ¬ IsStrongFFStarOffender (autI hV T) B := by
    rintro B ⟨hBo, hBr⟩
    obtain ⟨-, hBq, hBq2⟩ := hcore hBo
    rw [rAV_lt_one_iff hsq hBo.isA2, hBq] at hBr
    exact absurd hBr (not_lt.mpr hBq2)
  have hJnot : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hJ
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp h
  obtain ⟨_, A₀, hA₀off, rfl⟩ := (offenderImages_nonempty_iff_not_le hV (H := T)).mpr hJnot
  have hA₀max : IsMaxElemAbelian T A₀ := hA₀off.1
  have hA₀o : IsFFStarOffender (autI hV T) (autI hV A₀) :=
    offenderImages_isFFStarOffender hV hVT hTV ⟨A₀, hA₀off, rfl⟩
  obtain ⟨hA₀L, hA₀q, hA₀q2⟩ := hcore hA₀o
  have hA₀2 : IsPGroup 2 (autI hV A₀) := hA₀o.2.2.1.isPGroup
  have hA₀F : Nat.card (autI hV A₀) = Nat.card F := hA₀q.trans hF.symm
  have hT2' : IsPGroup 2 (autI hV T) := B2F.isPGroup_autI hV hT2 hTV
  have hoff : ∀ A, IsFFStarOffender (autI hV T) A → A ≤ autI hV A₀ := by
    intro A hA
    obtain ⟨hAL, -, -⟩ := hcore hA
    have hc := D.card_le_of_isPGroup hV hLV (sup_le hAL hA₀L)
      (hT2'.to_le (sup_le hA.1 hA₀o.1))
    have heq : autI hV A₀ = A ⊔ autI hV A₀ :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hA₀F]; exact hc)
    calc A ≤ A ⊔ autI hV A₀ := le_sup_left
      _ = autI hV A₀ := heq.symm
  have hrA : rkIdx (fixV (autI hV A₀)) = n := by
    have e := B1.card_eq_index_mul (autI hV A₀)
    rw [B1.index_eq_two_pow hsq] at e
    have hpos := B1.card_fixV_pos (autI hV A₀)
    have h1 : 2 ^ rkIdx (fixV (autI hV A₀)) * Nat.card (fixV (autI hV A₀)) ≤
        2 ^ n * Nat.card (fixV (autI hV A₀)) := by
      rw [← e, ← hA₀q]
      exact hoffV hA₀o
    have h2 : 2 ^ n * Nat.card (fixV (autI hV A₀)) ≤
        2 ^ rkIdx (fixV (autI hV A₀)) * Nat.card (fixV (autI hV A₀)) := by
      rw [← e]
      exact hA₀q2
    exact Nat.pow_right_injective (le_refl 2)
      (le_antisymm (Nat.le_of_mul_le_mul_right h1 hpos) (Nat.le_of_mul_le_mul_right h2 hpos))
  have hrL : 2 * n ≤ rkIdx (fixV (autI hV L)) := by
    have e := B1.card_eq_index_mul (autI hV L)
    rw [B1.index_eq_two_pow hsq] at e
    have hpos := B1.card_fixV_pos (autI hV L)
    have hW : Nat.card (Quasithin.H.StdMod (Fin 2) F) = 2 ^ n * 2 ^ n := by
      rw [Quasithin.H.card_stdMod, Fintype.card_fin, hF, sq]
    have hcent := D.card_mul_card_cent_le hVc hLV
    rw [hW, ← card_fixV_autI hV hLV] at hcent
    have h1 : 2 ^ (2 * n) * Nat.card (fixV (autI hV L)) ≤
        2 ^ rkIdx (fixV (autI hV L)) * Nat.card (fixV (autI hV L)) := by
      rw [← e, two_mul, pow_add]
      exact hcent
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h1 hpos)
  obtain ⟨ℓ, hℓL, hgen⟩ := D.exists_conj_gen hV hLV hA₀L hA₀2 hA₀F
  have hDE := hDE_of_offender hV hXV hLX hTX hT2 hA₂ hA₀max hℓL hgen (by rw [hrA]; exact hrL)
    hoff
  have hbT : baum T ≤ T := B2F.baum_le T
  have hA₀b : autI hV A₀ ≤ autI hV (baum T) :=
    autI_mono hV ((le_iSup₂_of_le A₀ hA₀max le_rfl : A₀ ≤ thompsonJ T).trans
      (B2F.thompsonJ_le_baum T))
  have hb2 : IsPGroup 2 (autI hV (baum T)) := hT2'.to_le (autI_mono hV hbT)
  have hbinf : autI hV (baum T) ⊓ autI hV L = autI hV A₀ := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf hA₀b hA₀L) ?_).symm
    rw [hA₀F]
    exact D.card_le_of_isPGroup hV hLV inf_le_right (hb2.to_le inf_le_left)
  have hSyl : IsSylowTwoOf (autI hV (baum T)) (autI hV L ⊔ autI hV (baum T)) := by
    refine C124.L2.isSylowTwoOf_sup_of_normalizing
      (C124.L2.autI_le_normalizer_of_le_normalizer hV (hbT.trans hTL)) hb2 ?_
    rw [hbinf]
    exact D.isSylowTwoOf_of_card hV hLV hA₀L hA₀2 hA₀F
  rw [sup_comm]
  exact (GC137.b2_19_rel hV hVX hXV hLodd hT2 hTX hVT hA₁ hA₂ hA₃ hB hC hDE).2 hSyl

end CFSG.Quasithin.B610T

end
