module

public import CFSG.Quasithin.Vol2.Ch11SecD556A
public import CFSG.Quasithin.Vol2.Ch11SecD551D
public import CFSG.Quasithin.Vol2.Ch11SecDFacts4
public import CFSG.Quasithin.Vol2.Ch11StatementsH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem cartan_le_normalizer_V₁ (hF : SecA.NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {V₁ X : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) :
    X ≤ Subgroup.normalizer (V₁ : Set G) := by
  intro x hx
  have hxL : x ∈ L := (hX.1 hx).1
  have hxT : x ∈ Subgroup.normalizer (TL T L : Set G) := (hX.1 hx).2
  have hxV : x ∈ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV h hxL
  have hV₁V : V₁ ≤ fsuV T I := SecA.IsVi.le_fsuV hV₁
  have hTLeq : TL T L ⊓ L = T ⊓ L := by
    change T ⊓ (L ⊔ pCoreOf 2 (L ⊔ T)) ⊓ L = T ⊓ L
    rw [inf_assoc, inf_eq_right.mpr (le_sup_left : L ≤ L ⊔ pCoreOf 2 (L ⊔ T))]
  have hxTL : x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [← hTLeq]
    exact mem_normalizer_inf hxT (Subgroup.le_normalizer hxL)
  have hσZ : SecA.conjV (fsuV T I) x hxV ∈
      SecA.stabW ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) := by
    rw [← SecA.inf_centralizer_subgroupOf, SecA.conjV_mem_stabW_iff inf_le_left hxV]
    exact mem_normalizer_inf hxV (SecA.mem_normalizer_centralizer (Subgroup.le_normalizer hxL))
  have hσH : ∀ g ∈ autOn L (fsuV T I),
      SecA.conjV (fsuV T I) x hxV * g * (SecA.conjV (fsuV T I) x hxV)⁻¹ ∈ autOn L (fsuV T I) :=
    fun g hg => (Subgroup.mem_normalizer_iff.mp (autOn_le_normalizer_autOn
      (Subgroup.le_normalizer : L ≤ _) (SecA.conjV_mem_autOn hxL hxV)) g).mp hg
  have hσP : ∀ g ∈ autOn (T ⊓ L) (fsuV T I),
      (SecA.conjV (fsuV T I) x hxV)⁻¹ * g * SecA.conjV (fsuV T I) x hxV ∈
        autOn (T ⊓ L) (fsuV T I) := by
    have hmem := autOn_le_normalizer_autOn
      (le_rfl : Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ _)
      (SecA.conjV_mem_autOn hxTL hxV)
    intro g hg
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmem) g).mp hg
    simpa using this
  have hflag := SecA.isFlagW_of_isVi h hV₁
  have hflag' := SecA.isFlagW_map hflag hσZ hσH hσP
  obtain ⟨U₁, U₂, U₃, -, -, -, -, -, huniq, -, -⟩ := SecA.hasUniqueFlag hF h1102 h
  have heq := (huniq _ hflag').trans (huniq _ hflag).symm
  exact (SecA.conjV_mem_stabW_iff hV₁V hxV).mp (SecA.mem_stabW_of_map_eq heq)

omit [Finite G] in
theorem normalizer_le_normalizer_Y (L V₁ : Subgroup G) :
    Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer
      ((Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) : Subgroup G) : Set G) := by
  intro g hg
  have hK := normalizer_le_normalizer_kOf L V₁ V₁ hg
  refine mem_normalizer_inf ?_ (mem_normalizer_sectionCentralizer hK
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hK))
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.centralizer_le_normalizer _)).mp inferInstance hg

theorem mem_sectionCentralizer_lOf {L V₁ : Subgroup G} {g : G}
    (hgL : g ∈ Subgroup.normalizer (LOf L V₁ : Set G))
    (hg : g ∈ sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) :
    g ∈ sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL₁K : LOf L V₁ ≤ KOf L V₁ V₁ := le_conjClosure _ _
  have hle : LOf L V₁ ⊓ pCoreOf 2 (KOf L V₁ V₁) ≤ pCoreOf 2 (LOf L V₁) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun l hl =>
        mem_normalizer_inf (Subgroup.le_normalizer hl)
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hL₁K hl)))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
  refine ⟨hgL, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hgL,
    fun l hl => hle ⟨?_, hg.2.2 l (hL₁K hl)⟩⟩
  exact (LOf L V₁).mul_mem ((Subgroup.mem_normalizer_iff.mp hgL l).mp hl) ((LOf L V₁).inv_mem hl)

theorem stmt11_5_6_five (hTI : PointsTIFact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1112 : Stmt11_1_2) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n)
    {V₁ X : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) :
    ⁅pCoreOf 2 (L ⊔ T), X⁆ ≤ pCoreOf 2 (KOf L V₁ V₁ ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := ((h1141 G T L I n V₁ X h hV₁ hX).2.2 _
    (kOf_cComp_centralizer hTI h1102 h1110 h1112 h1141 h1143 h hV₁) (le_conjClosure _ _)).2
  refine (Subgroup.commutator_mono ?_ le_rfl).trans h3
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_two_le_of_isSylowTwoOf
    (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right)
  exact le_ROf hOT (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    ((((perfectCore_le _).trans inf_le_left).trans le_sup_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))

theorem stmt11_5_6_one (hCart : CartanFact) (hF : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (h1141 : Stmt11_4_1) (h1151 : Stmt11_5_1) (h : Hyp11 G T L I n) {V₁ X : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) :
    Nat.Coprime (Nat.card ↥(Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)))) (2 ^ n - 1) := by
  obtain ⟨hXC, hE⟩ := hCart G T L I n V₁ X (natSetting11_of h1102 h1141 h hV₁)
    (h1151 G T L I n h) hV₁ hX
  have hXN := cartan_le_normalizer_V₁ hF h1102 h hV₁ hX
  have hV₁T : V₁ ≤ T := (SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)
  apply Nat.coprime_of_dvd
  intro p hp hpY hpq
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hn := h.one_lt
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
    rw [h2n] at hpq
    omega
  obtain ⟨E, hEX, hEab, hEcard⟩ := hE p hp hpq
  have hE2 : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hEab.2 x x.2)⟩
  have hEN := (hEX.trans hXN).trans (normalizer_le_normalizer_Y L V₁)
  obtain ⟨y, hyY, hyord, hyE⟩ := exists_orderOf_eq_of_isPGroup_normalizer hE2 hEN hpY
  have hyN : y ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hyY).1
  have hyE' : y ∉ E := by
    intro hyE'
    have hyL : y ∈ L := (hX.1 (hEX hyE')).1
    have hy1 : y ∈ X ⊓ Subgroup.centralizer (V₁ : Set G) ⊓
        sectionCentralizer (LOf L V₁) (pCoreOf 2 (LOf L V₁)) :=
      ⟨⟨hEX hyE', (Subgroup.mem_inf.mp hyY).1⟩, mem_sectionCentralizer_lOf
        (mem_normalizer_lOf (Subgroup.le_normalizer hyL) hyN) (Subgroup.mem_inf.mp hyY).2⟩
    rw [hXC, Subgroup.mem_bot] at hy1
    rw [hy1, orderOf_one] at hyord
    exact hp.one_lt.ne hyord
  have hF3 := isElemAbelian_sup_zpowers hEab (by rw [← hyord]; exact pow_orderOf_eq_one y) hyE
  have hcard := card_sup_zpowers_of_not_mem hyord hyE hyE'
  rw [hEcard, ← pow_succ] at hcard
  have hle : E ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le (hEX.trans hXN) (Subgroup.zpowers_le.mpr hyN)
  have := le_two_of_elemAbelian h.fsu.qtke.2.2 (SecA.IsVi.ne_bot h hV₁ le_rfl)
    (h.fsu.sylow.1.to_le hV₁T) hp hp2 hle hF3 hcard
  omega

end CFSG.Quasithin.Vol2.Ch11.SecD
