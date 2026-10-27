module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Blocks
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.A4Local

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L15412

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

variable {G : Type*} [Group G]

theorem pRank_autI_le [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V M : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMN : M ≤ Subgroup.normalizer (V : Set G))
    (h2 : IsPGroup 2 ↥(M ⊓ Subgroup.centralizer (V : Set G))) :
    CFSG.Open.pRank p (autI hV M) ≤ CFSG.Open.pRank p M := by
  set φ := convHom hV M hMN with hφ
  have hker : ¬ p ∣ Nat.card φ.ker := by
    rw [hφ, ker_convHom]
    have e : Nat.card ((M ⊓ Subgroup.centralizer (V : Set G)).subgroupOf M) =
        Nat.card ↥(M ⊓ Subgroup.centralizer (V : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [e]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    rw [hn]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow hdvd))
  have e1 : CFSG.Open.pRank p (⊤ : Subgroup (↥M ⧸ φ.ker)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥M) :=
    CFSG.SectionRank.pRank_quotient_eq φ.ker hker
  have e2 : (↥M ⧸ φ.ker) ≃* ↥(autI hV M) :=
    (QuotientGroup.quotientKerEquivRange φ).trans
      (MulEquiv.subgroupCongr (range_convHom hV M hMN))
  have e3 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt e2
  rw [← pRank_top_subtype (autI hV M), ← e3, e1, pRank_top_subtype]

section Preimage

variable {V M : Subgroup G} (hV : IsElemAbelian 2 V) (hMN : M ≤ Subgroup.normalizer (V : Set G))

theorem le_preI_autI {Y : Subgroup G} (hYM : Y ≤ M) : Y ≤ preI hV M hMN (autI hV Y) :=
  fun _ hy => (mem_preI hV).2 ⟨hYM hy, convI_mem_autI hV hy (hMN (hYM hy))⟩

theorem exists_mul_of_mem_preI {Y : Subgroup G} (hYM : Y ≤ M) {x : G}
    (hx : x ∈ preI hV M hMN (autI hV Y)) :
    ∃ y ∈ Y, ∃ c ∈ M ⊓ Subgroup.centralizer (V : Set G), x = y * c := by
  obtain ⟨hxM, hxY⟩ := (mem_preI hV).1 hx
  obtain ⟨g, hgY, hg⟩ := (mem_autI hV).1 hxY
  refine ⟨g, hgY, (g : G)⁻¹ * x, ⟨M.mul_mem (M.inv_mem (hYM hgY)) hxM, ?_⟩, by group⟩
  have h1 : convI hV (g⁻¹ * ⟨x, hMN hxM⟩) = 1 := by
    rw [map_mul, map_inv, hg]
    exact inv_mul_cancel _
  exact (convI_eq_one_iff hV _).1 h1

theorem exists_mul_of_convI_mem {Y : Subgroup G} (hYM : Y ≤ M) {x : G} (hxM : x ∈ M)
    (hxY : convI hV ⟨x, hMN hxM⟩ ∈ autI hV Y) :
    ∃ y ∈ Y, ∃ c ∈ M ⊓ Subgroup.centralizer (V : Set G), x = y * c :=
  exists_mul_of_mem_preI hV hMN hYM ((mem_preI hV).2 ⟨hxM, hxY⟩)

theorem eq_oTwoUpper_preI [Finite G] {Y : Subgroup G} (hYM : Y ≤ M) (hY : Y = oTwoUpper Y)
    (hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (h2 : IsPGroup 2 ↥(M ⊓ Subgroup.centralizer (V : Set G))) :
    Y = oTwoUpper (preI hV M hMN (autI hV Y)) := by
  refine eq_oTwoUpper_of_pow_mem (le_preI_autI hV hMN hYM) (fun x hx => ?_) hY
  obtain ⟨y, hy, c, hc, rfl⟩ := exists_mul_of_mem_preI hV hMN hYM hx
  obtain ⟨k, hk⟩ := h2 ⟨c, hc⟩
  have hk' : c ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hC hc) (2 ^ k)
  exact ⟨k, by rw [hpow, hk', mul_one]; exact hy'⟩

theorem oTwoUpper_eq_self {K : Type*} [Group K] {D : Subgroup K}
    (hD : ∀ x ∈ D, Odd (orderOf x)) : oTwoUpper D = D :=
  le_antisymm (oTwoUpper_le D) fun x hx => mem_oTwoUpper_of_odd hx (hD x hx)

@[expose] noncomputable def psi (D : Subgroup (MulAut (IntMod V hV))) : Subgroup G :=
  oTwoUpper (preI hV M hMN D)

theorem psi_le (D : Subgroup (MulAut (IntMod V hV))) : psi hV hMN D ≤ M :=
  (oTwoUpper_le _).trans (preI_le hV)

theorem psi_eq_oTwoUpper (D : Subgroup (MulAut (IntMod V hV))) :
    psi hV hMN D = oTwoUpper (psi hV hMN D) :=
  (A4.oTwoUpper_oTwoUpper _).symm

theorem autI_psi [Finite G] {D : Subgroup (MulAut (IntMod V hV))} (hDM : D ≤ autI hV M)
    (hD : ∀ x ∈ D, Odd (orderOf x)) : autI hV (psi hV hMN D) = D := by
  have hP : preI hV M hMN D ≤ Subgroup.normalizer (V : Set G) := (preI_le hV).trans hMN
  have h1 : autI hV (psi hV hMN D) = oTwoUpper (autI hV (preI hV M hMN D)) :=
    (A4.oTwoUpper_autOn hP).symm
  rw [h1, autI_preI hV hDM, oTwoUpper_eq_self hD]

theorem cjSub_preI {g : G} (hg : g ∈ M) (D : Subgroup (MulAut (IntMod V hV))) :
    cjSub g (preI hV M hMN D) = preI hV M hMN (B1.conjAut (convI hV ⟨g, hMN hg⟩) D) := by
  ext x
  rw [mem_cjSub, mem_preI, mem_preI]
  have hiff : g⁻¹ * x * g ∈ M ↔ x ∈ M := by
    constructor
    · intro h
      have := M.mul_mem (M.mul_mem hg h) (M.inv_mem hg)
      simpa [mul_assoc] using this
    · intro h
      exact M.mul_mem (M.mul_mem (M.inv_mem hg) h) hg
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hiff.mp h1, ?_⟩
    rw [B1.mem_conjAut]
    have e : (⟨g⁻¹ * x * g, hMN h1⟩ : Subgroup.normalizer (V : Set G)) =
        (⟨g, hMN hg⟩ : Subgroup.normalizer (V : Set G))⁻¹ * ⟨x, hMN (hiff.mp h1)⟩ *
          ⟨g, hMN hg⟩ := rfl
    have h2' : convI hV ⟨g⁻¹ * x * g, hMN h1⟩ ∈ D := h2
    rw [e, map_mul, map_mul, map_inv] at h2'
    exact h2'
  · rintro ⟨h1, h2⟩
    refine ⟨hiff.mpr h1, ?_⟩
    rw [B1.mem_conjAut] at h2
    have e : (⟨g⁻¹ * x * g, hMN (hiff.mpr h1)⟩ : Subgroup.normalizer (V : Set G)) =
        (⟨g, hMN hg⟩ : Subgroup.normalizer (V : Set G))⁻¹ * ⟨x, hMN h1⟩ * ⟨g, hMN hg⟩ := rfl
    show convI hV ⟨g⁻¹ * x * g, hMN (hiff.mpr h1)⟩ ∈ D
    rw [e, map_mul, map_mul, map_inv]
    exact h2

theorem cjSub_psi [Finite G] {g : G} (hg : g ∈ M) (D : Subgroup (MulAut (IntMod V hV))) :
    cjSub g (psi hV hMN D) = psi hV hMN (B1.conjAut (convI hV ⟨g, hMN hg⟩) D) := by
  unfold psi
  rw [← cjSub_preI hV hMN hg D]
  exact (oTwoUpper_map (MulAut.conj g).toMonoidHom _).symm

theorem mem_normalizer_psi [Finite G] {g : G} (hg : g ∈ M) {D : Subgroup (MulAut (IntMod V hV))}
    (hgD : B1.conjAut (convI hV ⟨g, hMN hg⟩) D = D) :
    g ∈ Subgroup.normalizer (psi hV hMN D : Set G) := by
  rw [mem_normalizer_iff_cjSub_eq, cjSub_psi hV hMN hg, hgD]

theorem eq_psi_autI [Finite G] {Y : Subgroup G} (hYM : Y ≤ M) (hY : Y = oTwoUpper Y)
    (hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (h2 : IsPGroup 2 ↥(M ⊓ Subgroup.centralizer (V : Set G))) :
    Y = psi hV hMN (autI hV Y) :=
  eq_oTwoUpper_preI hV hMN hYM hY hC h2

theorem inf_centralizer_le_normalizer_psi [Finite G] (D : Subgroup (MulAut (IntMod V hV))) :
    M ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (psi hV hMN D : Set G) := by
  intro c hc
  refine mem_normalizer_psi hV hMN hc.1 ?_
  have h1 : convI hV ⟨c, hMN hc.1⟩ = 1 := (convI_eq_one_iff hV _).2 hc.2
  ext x
  rw [B1.mem_conjAut, h1]
  simp

end Preimage

theorem pCoreOf_eq_inf_centralizer [Finite G] {V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (hodd : Odd (Nat.card (autI hV Y)))
    (h2 : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer (V : Set G))) :
    pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · refine le_inf (pCoreOf_le 2 Y) ?_
    have hO : pCoreOf 2 Y ≤ Subgroup.normalizer (V : Set G) := (pCoreOf_le 2 Y).trans hYV
    rw [← autI_eq_bot_iff hV hO]
    have hp : IsPGroup 2 (autI hV (pCoreOf 2 Y)) :=
      B2F.isPGroup_autI hV (pCoreOf_isPGroup 2 Y) hO
    have hle : autI hV (pCoreOf 2 Y) ≤ autI hV Y := autI_mono hV (pCoreOf_le 2 Y)
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hn] at hdvd
    rcases n with _ | n
    · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hn)
    · exfalso
      have h2' : 2 ∣ Nat.card (autI hV Y) := (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2')
  · exact le_pCoreOf_of_le_normalizer 2 inf_le_left
      (B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hYV)) h2

theorem relIndex_pCoreOf_eq [Finite G] {V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (hodd : Odd (Nat.card (autI hV Y)))
    (h2 : IsPGroup 2 ↥(Y ⊓ Subgroup.centralizer (V : Set G))) :
    (pCoreOf 2 Y).relIndex Y = Nat.card (autI hV Y) := by
  rw [pCoreOf_eq_inf_centralizer hV hYV hodd h2, card_autI_eq hV hYV]

section Shape

variable [Finite G] {V : Subgroup G} {hV : IsElemAbelian 2 V} {M T : Subgroup G}
  {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

theorem blocks_card_le_two (B : E2.Blocks hV M 𝓗 I) (hred : IsTwoReducedIn M V)
    (h2 : IsPGroup 2 ↥(M ⊓ Subgroup.centralizer (V : Set G)))
    (h3 : CFSG.Open.pRank 3 M ≤ 2) : I.card ≤ 2 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨L₁, hL₁, L₂, hL₂, L₃, hL₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
  obtain ⟨f₁, hf₁, -, h3₁⟩ := B.exists_orderOf_eq_three hL₁
  obtain ⟨f₂, hf₂, -, h3₂⟩ := B.exists_orderOf_eq_three hL₂
  obtain ⟨f₃, hf₃, -, h3₃⟩ := B.exists_orderOf_eq_three hL₃
  have hb := B.hb
  have s₁ := B.sub hL₁
  have s₂ := B.sub hL₂
  have s₃ := B.sub hL₃
  have hZ₁ : Subgroup.zpowers f₁ ≤ L₁ := Subgroup.zpowers_le.mpr hf₁
  have hZ₂ : Subgroup.zpowers f₂ ≤ L₂ := Subgroup.zpowers_le.mpr hf₂
  have hZ₃ : Subgroup.zpowers f₃ ≤ L₃ := Subgroup.zpowers_le.mpr hf₃
  have c12 : ∀ a ∈ Subgroup.zpowers f₁, ∀ b ∈ Subgroup.zpowers f₂, a * b = b * a :=
    fun a ha b hb' => hb.comm L₁ s₁ L₂ s₂ h12 a (hZ₁ ha) b (hZ₂ hb')
  have hZ12 : Nat.card ↥(Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂) = 9 := by
    have h := card_sup_mul_card_inf_of_commute c12
    have hinf : Subgroup.zpowers f₁ ⊓ Subgroup.zpowers f₂ = ⊥ :=
      le_bot_iff.1 ((inf_le_inf hZ₁ hZ₂).trans (inf_eq_bot_of_ne hb s₁ s₂ h12).le)
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, h3₁, h3₂] at h
    exact h
  have c123 : ∀ a ∈ Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂, ∀ c ∈ Subgroup.zpowers f₃,
      a * c = c * a := by
    intro a ha c hc
    have hN : Subgroup.zpowers f₂ ≤
        Subgroup.normalizer ((Subgroup.zpowers f₁ : Subgroup _) : Set (MulAut (IntMod V hV))) :=
      E2.le_normalizer_of_commute fun b hb' a ha => (c12 a ha b hb').symm
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_exists_mul hN).mp ha
    have e1 := hb.comm L₁ s₁ L₃ s₃ h13 x (hZ₁ hx) c (hZ₃ hc)
    have e2 := hb.comm L₂ s₂ L₃ s₃ h23 y (hZ₂ hy) c (hZ₃ hc)
    rw [mul_assoc, e2, ← mul_assoc, e1, mul_assoc]
  have hinf3 : (Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂) ⊓ Subgroup.zpowers f₃ = ⊥ := by
    have hle : Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ≤
        ⨆ L ∈ 𝓗, ⨆ (_ : L ≠ L₃), L :=
      sup_le (hZ₁.trans (le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut (IntMod V hV)))
        (_ : H' ∈ 𝓗) => ⨆ (_ : H' ≠ L₃), H') L₁ s₁ (le_iSup_of_le h13 le_rfl)))
        (hZ₂.trans (le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut (IntMod V hV)))
        (_ : H' ∈ 𝓗) => ⨆ (_ : H' ≠ L₃), H') L₂ s₂ (le_iSup_of_le h23 le_rfl)))
    refine le_bot_iff.1 ?_
    rw [inf_comm]
    exact (inf_le_inf hZ₃ hle).trans (hb.inf_biSup_ne_eq_bot s₃).le
  have hcard : Nat.card ↥(Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ⊔ Subgroup.zpowers f₃) =
      3 ^ 3 := by
    have h := card_sup_mul_card_inf_of_commute c123
    rw [hinf3, Subgroup.card_bot, mul_one, hZ12, Nat.card_zpowers, h3₃] at h
    rw [h]
    norm_num
  have hp : ∀ {f : MulAut (IntMod V hV)}, orderOf f = 3 → f ^ 3 = 1 := fun hf => by
    rw [← hf]
    exact pow_orderOf_eq_one _
  have hel : IsElemAbelian 3 (Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ⊔
      Subgroup.zpowers f₃) :=
    isElemAbelian_sup (isElemAbelian_sup (isElemAbelian_zpowers (hp h3₁))
      (isElemAbelian_zpowers (hp h3₂)) c12) (isElemAbelian_zpowers (hp h3₃)) c123
  have hle : Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ⊔ Subgroup.zpowers f₃ ≤ autI hV M :=
    sup_le (sup_le (hZ₁.trans (B.le_autI hL₁)) (hZ₂.trans (B.le_autI hL₂)))
      (hZ₃.trans (B.le_autI hL₃))
  have h1 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hle hel hcard
  have h4 := pRank_autI_le (p := 3) (by norm_num) hV hred.2.1 h2
  omega

theorem shape (B : E2.Blocks hV M 𝓗 I) (hred : IsTwoReducedIn M V) (hT : IsSylowTwoOf T M)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hI2 : I.card ≤ 2)
    {D : Subgroup (MulAut (IntMod V hV))} (hDJ : D ≤ autI hV (thompsonJ M))
    (hDodd : D = oTwoUpper D)
    (hDT : autI hV T ≤ Subgroup.normalizer (D : Set (MulAut (IntMod V hV))))
    (hD1 : D ≠ ⊥) :
    (∃ L ∈ I, ∃ f ∈ L, orderOf f = 3 ∧ D = Subgroup.zpowers f ∧
        ∀ g ∈ autI hV M, B1.conjAut g L = L) ∨
      (∃ L₁ ∈ I, ∃ L₂ ∈ I, L₁ ≠ L₂ ∧ (∀ L ∈ I, L = L₁ ∨ L = L₂) ∧
        ∃ f₁ ∈ L₁, ∃ f₂ ∈ L₂, orderOf f₁ = 3 ∧ orderOf f₂ = 3 ∧
          D = Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂) := by
  classical
  have hpos := (B.nonempty hT hred hJ).card_pos
  have hsyl := isSylowTwoOf_autI hV hred.2.1 hT
  have hperm : ∀ g ∈ autI hV M, ∀ L ∈ I, B1.conjAut g L ∈ I := fun g hg L hL =>
    B.conjAut_mem hg hL
  have hdata : ∀ L ∈ I, ∃ f ∈ L, orderOf f = 3 ∧
      ∃ t ∈ L, t ∈ autI hV T ∧ t * f * t⁻¹ = f⁻¹ := by
    intro L hL
    obtain ⟨f, hfL, -, hf3⟩ := B.exists_orderOf_eq_three hL
    obtain ⟨t, htL, htT, -, ht2⟩ := B.exists_orderOf_eq_two hred hT hL
    exact ⟨f, hfL, hf3, t, htL, htT,
      conj_eq_inv (B.card_eq hL) hfL htL hf3 (B.mul_ne_mul hL htL hfL ht2 hf3)⟩
  have hDle : ∀ X : Subgroup (MulAut (IntMod V hV)),
      (∀ x ∈ autI hV (thompsonJ M), Odd (orderOf x) → x ∈ X) → D ≤ X := by
    intro X hX
    rw [hDodd]
    exact (Subgroup.closure_le X).mpr fun x hx => hX x (hDJ hx.1) hx.2
  rcases (by omega : I.card = 1 ∨ I.card = 2) with h1 | h2
  · obtain ⟨L₁, hI⟩ := Finset.card_eq_one.mp h1
    have hL₁ : L₁ ∈ I := by rw [hI]; exact Finset.mem_singleton_self _
    have hI' : ∀ L ∈ I, L = L₁ := fun L hL => by rw [hI] at hL; exact Finset.mem_singleton.mp hL
    obtain ⟨f, hfL, hf3, -⟩ := hdata L₁ hL₁
    have hJM : autI hV (thompsonJ M) = L₁ := by rw [B.eq, E2.iSup_eq_of_singleton hL₁ hI']
    have hDf : D ≤ Subgroup.zpowers f := hDle _ fun x hx hodd =>
      mem_zpowers_of_odd (B.card_eq hL₁) hfL hf3 (hJM ▸ hx) hodd
    rcases eq_bot_or_eq_of_le_zpowers hf3 hDf with h | h
    · exact absurd h hD1
    · exact Or.inl ⟨L₁, hL₁, f, hfL, hf3, h, fun g hg => hI' _ (hperm g hg L₁ hL₁)⟩
  · obtain ⟨L₁, L₂, h12, hI⟩ := Finset.card_eq_two.mp h2
    have hL₁ : L₁ ∈ I := by rw [hI]; simp
    have hL₂ : L₂ ∈ I := by rw [hI]; simp
    have hI' : ∀ L ∈ I, L = L₁ ∨ L = L₂ := fun L hL => by rw [hI] at hL; simpa using hL
    obtain ⟨f₁, hf₁, h3₁, t₁, ht₁, ht₁T, hi₁⟩ := hdata L₁ hL₁
    obtain ⟨f₂, hf₂, h3₂, t₂, ht₂, ht₂T, hi₂⟩ := hdata L₂ hL₂
    have s₁ := B.sub hL₁
    have s₂ := B.sub hL₂
    have hJM : autI hV (thompsonJ M) = L₁ ⊔ L₂ := by rw [B.eq, E2.iSup_eq_of_pair hL₁ hL₂ hI']
    have hDF : D ≤ Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ := hDle _ fun x hx hodd =>
      mem_sup_zpowers_of_odd B.hb s₁ s₂ h12 hf₁ hf₂ h3₁ h3₂ (hJM ▸ hx) hodd
    have hfix : ∀ {L L' : Subgroup (MulAut (IntMod V hV))} {f : MulAut (IntMod V hV)},
        L ∈ I → L' ∈ I → L ≠ L' → (∀ L'' ∈ I, L'' = L ∨ L'' = L') → f ∈ L →
        orderOf f = 3 → D = Subgroup.zpowers f → ∀ g ∈ autI hV M, B1.conjAut g L = L := by
      intro L L' f hL hL' hne hI'' hfL hf3 hDf g hg
      refine conjAut_eq_of_isSylowTwoOf hsyl hL hne hI'' hperm hL' (fun t ht => ?_) g hg
      have hmem : t * f * t⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (hDT ht) f).mp (hDf ▸ Subgroup.mem_zpowers f)
      rcases hI'' _ (hperm t (autI_mono hV hT.1 ht) L hL) with h | h
      · exact h
      · exfalso
        have hf1 : t * f * t⁻¹ ≠ 1 := by
          intro h1
          have hf1' : f = 1 := by
            calc f = t⁻¹ * (t * f * t⁻¹) * t := by group
              _ = 1 := by rw [h1]; group
          rw [hf1', orderOf_one] at hf3
          norm_num at hf3
        have hm1 : t * f * t⁻¹ ∈ L' := by
          rw [← h, B1.mem_conjAut]
          have e : t⁻¹ * (t * f * t⁻¹) * t = f := by group
          rw [e]
          exact hfL
        have hm2 : t * f * t⁻¹ ∈ L := Subgroup.zpowers_le.mpr hfL (hDf ▸ hmem)
        have hm : t * f * t⁻¹ ∈ L ⊓ L' := ⟨hm2, hm1⟩
        rw [inf_eq_bot_of_ne B.hb (B.sub hL) (B.sub hL') hne, Subgroup.mem_bot] at hm
        exact hf1 hm
    rcases eq_of_le_sup_zpowers B.hb s₁ s₂ h12 hf₁ hf₂ h3₁ h3₂ ht₁ ht₂ hi₁ hi₂ (hDT ht₁T)
      (hDT ht₂T) hDF with h | h | h | h
    · exact absurd h hD1
    · exact Or.inl ⟨L₁, hL₁, f₁, hf₁, h3₁, h, hfix hL₁ hL₂ h12 hI' hf₁ h3₁ h⟩
    · exact Or.inl ⟨L₂, hL₂, f₂, hf₂, h3₂, h, hfix hL₂ hL₁ (Ne.symm h12)
        (fun L hL => (hI' L hL).symm) hf₂ h3₂ h⟩
    · exact Or.inr ⟨L₁, hL₁, L₂, hL₂, h12, hI', f₁, hf₁, f₂, hf₂, h3₁, h3₂, h⟩

theorem conjAut_zpowers_of_fix (B : E2.Blocks hV M 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) {f : MulAut (IntMod V hV)} (hf : f ∈ L) (hf3 : orderOf f = 3)
    (hfix : ∀ g ∈ autI hV M, B1.conjAut g L = L) :
    ∀ g ∈ autI hV M, B1.conjAut g (Subgroup.zpowers f) = Subgroup.zpowers f :=
  fun g hg => conjAut_zpowers_eq B.hb (B.sub hL) (hfix g hg) hf hf hf3 hf3

theorem conjAut_sup_zpowers (B : E2.Blocks hV M 𝓗 I) {L₁ L₂ : Subgroup (MulAut (IntMod V hV))}
    (hL₁ : L₁ ∈ I) (hL₂ : L₂ ∈ I) (h12 : L₁ ≠ L₂) (hI' : ∀ L ∈ I, L = L₁ ∨ L = L₂)
    {f₁ f₂ : MulAut (IntMod V hV)} (hf₁ : f₁ ∈ L₁) (hf₂ : f₂ ∈ L₂) (h3₁ : orderOf f₁ = 3)
    (h3₂ : orderOf f₂ = 3) :
    ∀ g ∈ autI hV M, B1.conjAut g (Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂) =
      Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ := by
  intro g hg
  rw [conjAut_eq_map, Subgroup.map_sup, ← conjAut_eq_map, ← conjAut_eq_map]
  rcases hI' _ (B.conjAut_mem hg hL₁) with h | h
  · have h' : B1.conjAut g L₂ = L₂ := (hI' _ (B.conjAut_mem hg hL₂)).resolve_left
      fun e => h12 (conjAut_injective g (h.trans e.symm))
    rw [conjAut_zpowers_eq B.hb (B.sub hL₁) h hf₁ hf₁ h3₁ h3₁,
      conjAut_zpowers_eq B.hb (B.sub hL₂) h' hf₂ hf₂ h3₂ h3₂]
  · have h' : B1.conjAut g L₂ = L₁ := (hI' _ (B.conjAut_mem hg hL₂)).resolve_right
      fun e => h12 (conjAut_injective g (h.trans e.symm))
    rw [conjAut_zpowers_eq B.hb (B.sub hL₂) h hf₁ hf₂ h3₁ h3₂,
      conjAut_zpowers_eq B.hb (B.sub hL₁) h' hf₂ hf₁ h3₂ h3₁, sup_comm]

end Shape

end L15412

end CFSG.Quasithin.EmptyFaithfulMultiple
