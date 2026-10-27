module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338Fac
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRT

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem autOn_commute' {X Y V : Subgroup G}
    (hXY : ⁅X, Y⁆ ≤ Subgroup.centralizer (V : Set G)) :
    ∀ a ∈ autOn X V, ∀ b ∈ autOn Y V, a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp ha
  obtain ⟨y, hy, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp hb
  have hc : ((⁅x, y⁆ : Subgroup.normalizer (V : Set G)) : G) ∈
      Subgroup.centralizer (V : Set G) :=
    hXY (Subgroup.commutator_mem_commutator hx hy)
  have h1 := InternalSec.conjAct_eq_one_of_mem_centralizer _ hc
  have e : x * y = ⁅x, y⁆ * (y * x) := by rw [commutatorElement_def]; group
  rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]

theorem two_pow_mem_autOn {N T V : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) :
    ∀ x ∈ autOn (N ⊔ T) V, ∃ e : ℕ, x ^ 2 ^ e ∈ autOn N V := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.mp hx
  obtain ⟨e, he⟩ := InternalSec.two_of_sup hT hTN _ hg
  refine ⟨e, CFSG.QuasithinUnique.Setup.mem_autOn_iff.mpr ⟨g ^ 2 ^ e, ?_, ?_⟩⟩
  · simpa using he
  · rw [map_pow]

variable [Finite G]

theorem exists_ffStarOffender {T H₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hred : IsTwoReducedIn H₀ V) (hT : IsSylowTwoOf T H₀)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ∃ A : Subgroup (MulAut (IntMod V hV)), IsFFStarOffender (autI hV H₀) A := by
  obtain ⟨A, hA, hAC⟩ : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra h
    push Not at h
    exact hJ (iSup₂_le fun A hA => h A hA)
  exact ⟨_, offenderImages_isFFStarOffender hV hred.1 hred.2.1
    ⟨A, ⟨isMaxElemAbelian_of_isSylowTwoOf hT hA, hAC⟩, rfl⟩⟩

theorem le_ffJ_of_simple {W : Type} [CommGroup W] [Finite W]
    {X K₁ K₂ A : Subgroup (MulAut W)} {s : MulAut W} (hs₁ : IsSimpleGroup ↥K₁)
    (hperf₁ : ⁅K₁, K₁⁆ = K₁) (hsX : s ∈ X) (hK₂eq : K₂ = K₁.map (MulAut.conj s).toMonoidHom)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hKX : K₁ ⊔ K₂ ≤ X)
    (hXK : X ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (MulAut W)) : Set (MulAut W)))
    (h2X : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ K₁ ⊔ K₂) (hO2 : pCoreOf 2 X = ⊥)
    (hA : IsFFStarOffender X A) : K₁ ≤ ffJ X ∧ K₂ ≤ ffJ X := by
  set J := ffJ X with hJdef
  have hJX : J ≤ X := B6.ffJ_le X
  have hXJ : X ≤ Subgroup.normalizer (J : Set (MulAut W)) := B6.le_normalizer_ffJ X
  have hAJ : A ≤ J := B6.le_ffJ hA
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set (MulAut W)) :=
    Ch3Sec3.le_normalizer_of_commute hc
  have hKN₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hK₂N
  have hK₁K : K₁ ≤ K₁ ⊔ K₂ := le_sup_left
  have hK₁J : K₁ ≤ J := by
    rcases Ch3Sec3.le_or_commute_of_isSimpleGroup hs₁ hperf₁ ((hK₁K.trans hKX).trans hXJ)
        (((Subgroup.commutator_mono hK₁K hJX).trans
          (Ch3Sec3.commutator_le_left_of_le_normalizer hXK)).trans hKN₁) with hle | hcomm
    · exact hle
    · exfalso
      have hsJ : ∀ j ∈ J, s⁻¹ * j * s⁻¹⁻¹ ∈ J := fun j hj =>
        (Subgroup.mem_normalizer_iff.mp (inv_mem (hXJ hsX)) j).mp hj
      have hcomm₂ : ∀ b ∈ K₂, ∀ j ∈ J, b * j = j * b := by
        intro b hb j hj
        rw [hK₂eq] at hb
        obtain ⟨a, ha, rfl⟩ := hb
        have h1 := hcomm a ha _ (hsJ j hj)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1 ⊢
        calc s * a * s⁻¹ * j = s * (a * (s⁻¹ * j * s)) * s⁻¹ := by group
          _ = s * (s⁻¹ * j * s * a) * s⁻¹ := by rw [h1]
          _ = j * (s * a * s⁻¹) := by group
      have hJC : J ≤ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup (MulAut W)) : Set (MulAut W)) := by
        rw [Subgroup.le_centralizer_iff]
        exact sup_le
          (fun a ha => Subgroup.mem_centralizer_iff.mpr fun j hj => (hcomm a ha j hj).symm)
          (fun b hb => Subgroup.mem_centralizer_iff.mpr fun j hj => (hcomm₂ b hb j hj).symm)
      apply hA.2.1
      rw [eq_bot_iff]
      intro a ha
      refine Subgroup.mem_bot.mpr (Ch3Sec3.eq_one_of_two_of_commute hXK h2X hO2 (hA.1 ha)
        (fun k hk => (Subgroup.mem_centralizer_iff.mp (hJC (hAJ ha)) k hk)) (e := 1) ?_)
      simpa using hA.2.2.1.2 a ha
  refine ⟨hK₁J, ?_⟩
  rw [hK₂eq]
  rintro _ ⟨a, ha, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hXJ hsX) a).mp (hK₁J ha)

end CFSG.Quasithin.Vol2.Ch10.SecB.KRT
