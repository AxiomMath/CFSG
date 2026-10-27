module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteen
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

namespace TwelveEighteen

theorem conj_mem_barSub {M V₀ V X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMX : M ≤ normalizer (X : Set G)) :
    ∀ m ∈ Mbar M V₀ V hV, ∀ x ∈ barSub V₀ V hV X, m * x * m⁻¹ ∈ barSub V₀ V hV X := by
  intro m hm x hx
  obtain ⟨a, haM, rfl⟩ := (mem_barSub V₀ V hV M m).1 hm
  obtain ⟨b, hbX, rfl⟩ := (mem_barSub V₀ V hV X x).1 hx
  refine (mem_barSub V₀ V hV X _).2 ⟨a * b * a⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  show (a : G) * (b : G) * (a : G)⁻¹ ∈ X
  exact (mem_normalizer_iff.1 (hMX haM) b).1 hbX

theorem even_relIndex_cTilde_of_not_twoReduced {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀V : V₀ ≤ V) (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hirr : ConjGenerated M V₀ V) (hne : V₀ ≠ V) (hnot : ¬ TwoReduced M V) :
    Even ((M ⊓ centralizer (V : Set G)).relIndex (F11.CTilde M V₀ V)) := by
  classical
  obtain ⟨K, hKM, hMK, hCK, ⟨n, hn⟩, hKC⟩ : ∃ K : Subgroup G, K ≤ M ∧
      M ≤ normalizer (K : Set G) ∧ M ⊓ centralizer (V : Set G) ≤ K ∧
      (∃ n : ℕ, ((centralizer (V : Set G)).subgroupOf K).index = 2 ^ n) ∧
      ¬ K ≤ centralizer (V : Set G) := by
    by_contra hc
    apply hnot
    intro K hKM hMK hCK hidx
    by_contra hKC
    exact hc ⟨K, hKM, hMK, hCK, hidx, hKC⟩
  haveI : Nontrivial (Vtil V₀ V hV) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h1 : Nat.card (Vtil V₀ V hV) ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hnt
    have hc := card_Vtil_eq V₀ V hV hV₀V
    have h2 : Nat.card V ≤ Nat.card V₀ := by
      rw [hc]
      calc Nat.card V₀ * Nat.card (Vtil V₀ V hV)
          ≤ Nat.card V₀ * 1 := Nat.mul_le_mul_left _ h1
        _ = Nat.card V₀ := mul_one _
    exact hne (Subgroup.eq_of_le_of_card_ge hV₀V h2)
  have hNorm : ((centralizer (V : Set G)).subgroupOf K).Normal := by
    refine ⟨fun c hc k => ?_⟩
    rw [Subgroup.mem_subgroupOf, mem_centralizer_iff] at hc ⊢
    intro v hv
    have hkN := hM (hKM k.2)
    have hv' : (k : G)⁻¹ * v * (k : G) ∈ V := by
      have := (mem_normalizer_iff''.1 hkN v).1 hv
      simpa [mul_assoc] using this
    have e := hc _ hv'
    show v * ((k * c * k⁻¹ : ↥K) : G) = ((k * c * k⁻¹ : ↥K) : G) * v
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc v * ((k : G) * (c : G) * (k : G)⁻¹)
        = (k : G) * (((k : G)⁻¹ * v * (k : G)) * (c : G)) * (k : G)⁻¹ := by group
      _ = (k : G) * ((c : G) * ((k : G)⁻¹ * v * (k : G))) * (k : G)⁻¹ := by rw [e]
      _ = (k : G) * (c : G) * (k : G)⁻¹ * v := by group
  have hpow : ∀ x ∈ K, x ^ (2 ^ n) ∈ centralizer (V : Set G) := by
    intro x hx
    have h1 := Subgroup.pow_index_mem ((centralizer (V : Set G)).subgroupOf K) (⟨x, hx⟩ : ↥K)
    rw [hn, Subgroup.mem_subgroupOf] at h1
    simpa using h1
  have hP2 : IsPGroup 2 ↥(barSub V₀ V hV K) := by
    intro φ
    obtain ⟨a, haK, ha⟩ := (mem_barSub V₀ V hV K φ).1 φ.2
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← ha, ← map_pow, Subgroup.coe_one]
    rw [actTil_eq_one_iff]
    intro v hv
    have hc := mem_centralizer_iff.1 (hpow _ haK) v hv
    have : ((a ^ (2 ^ n) : ↥(stabTil V₀ V)) : G) = (a : G) ^ (2 ^ n) := by simp
    rw [this, ← hc]
    simp [V₀.one_mem]
  have hKbar : barSub V₀ V hV K = ⊥ :=
    eq_bot_of_isPGroup_of_stable hV hM hM₀ hirr hP2 (conj_mem_barSub hV hMK)
  have hKCt : K ≤ F11.CTilde M V₀ V := (barSub_eq_bot_iff hV hM hM₀ hKM).1 hKbar
  have hmul := Subgroup.relIndex_mul_relIndex (M ⊓ centralizer (V : Set G)) K
    (F11.CTilde M V₀ V) hCK hKCt
  have hidx : (M ⊓ centralizer (V : Set G)).relIndex K = 2 ^ n := by
    rw [← hn]
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨hKM x.2, h⟩⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hKC
    intro x hx
    have h1 : (centralizer (V : Set G)).subgroupOf K = ⊤ := Subgroup.index_eq_one.1 hn
    have h2 : (⟨x, hx⟩ : ↥K) ∈ (centralizer (V : Set G)).subgroupOf K := by
      rw [h1]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 h2
  rw [← hmul, hidx, even_iff_two_dvd]
  exact (dvd_pow_self 2 hn0).mul_right _

theorem uniqueMax_inf_normalizer_of_isSylowOf (D : Data G) {V : Subgroup G}
    (hV1 : InCalV1 D.M D.T V)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ centralizer (V : Set G))
      (D.M ⊓ centralizer (V : Set G)))
    {Q : Subgroup G} (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q (D.M ⊓ centralizer (V : Set G))) :
    UniqueMax D.M (D.M ⊓ normalizer (Q : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hkQ⟩ := hT.exists_mem_conj hQ
  have hkM : k ∈ D.M := (Subgroup.mem_inf.1 hk).1
  have hQeq : Q = conjSubgroup (D.T ⊓ centralizer (V : Set G)) k⁻¹ := by
    ext x
    rw [mem_conjSubgroup_iff, hkQ x, inv_inv]
  have hM : conjSubgroup D.M k⁻¹ = D.M :=
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (D.M.inv_mem hkM))
  have key : conjSubgroup (D.M ⊓ normalizer
      ((D.T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) k⁻¹ =
      D.M ⊓ normalizer (Q : Set G) := by
    rw [E3.conjSubgroup_inf, E3.conjSubgroup_normalizer, hM, ← hQeq]
  have h1 := uniqueMax_conjSubgroup hV1.2 k⁻¹
  rwa [hM, key] at h1

end TwelveEighteen

theorem weakClosureSetting_of_hyp125 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) : WeakClosureSetting D V₀ V := by
  have hP := h.pairFacts
  obtain ⟨h0, hcu, -⟩ : InCalV0 D.M V₀ V ∧ CentralizersUnique D.M D.T ∧
      ∀ W : Subgroup G, ¬ InCalW D.M D.T W := by
    rcases h.1 with ⟨-, h0⟩ | h2
    · exact absurd h0 hV₀
    · exact h2
  obtain ⟨hV₀in, hVin, hle, hTI₀, hTI, hgen, hnot⟩ := h0
  have h11 := h1114 V₀ V (Hyp125.hyp11 h127 h)
  have hne : V₀ ≠ V := fun e => hTI (e ▸ hTI₀)
  exact
    { pair := hP
      normalizer_eq := h.normalizer_eq
      ti₀ := fun _ => ⟨hTI₀, hne⟩
      normalizer₀ := fun _ => normalizer_eq_of_inCalV D hV₀in
      gen := fun _ => hgen
      even := fun _ => TwelveEighteen.even_relIndex_cTilde_of_not_twoReduced hP.elemAbelian hle
        hP.le_normalizer hP.le_normalizer₀ (fun v hv hv0 => (hgen v hv hv0).symm) hne hnot
      v1 := fun _ hQ => TwelveEighteen.uniqueMax_inf_normalizer_of_isSylowOf D
        (uc22p22n_inCalV1_of_not_isTI D hx h61 hVin hTI) (by
          haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          have hCM : centralizer (V : Set G) ≤ D.M := centralizer_le_of_inCalV D hVin
          have hMN : D.M ≤ normalizer (centralizer (V : Set G) : Set G) := by
            intro m hm
            rw [mem_normalizer_iff]
            intro c
            have hmV := mem_normalizer_iff.1 (hP.le_normalizer hm)
            constructor
            · intro hc
              rw [mem_centralizer_iff] at hc ⊢
              intro v hv
              have hv' : m⁻¹ * v * m ∈ V := by
                simpa [mul_assoc] using (mem_normalizer_iff''.1 (hP.le_normalizer hm) v).1 hv
              have e := hc _ hv'
              calc v * (m * c * m⁻¹) = m * ((m⁻¹ * v * m) * c) * m⁻¹ := by group
                _ = m * (c * (m⁻¹ * v * m)) * m⁻¹ := by rw [e]
                _ = m * c * m⁻¹ * v := by group
            · intro hc
              rw [mem_centralizer_iff] at hc ⊢
              intro v hv
              have hv' : m * v * m⁻¹ ∈ V := (hmV v).1 hv
              have e := hc _ hv'
              have e2 : m * v * m⁻¹ * (m * c * m⁻¹) = m * (v * c) * m⁻¹ := by group
              have e3 : m * c * m⁻¹ * (m * v * m⁻¹) = m * (c * v) * m⁻¹ := by group
              rw [e2, e3] at e
              exact mul_left_cancel (mul_right_cancel e)
          rw [inf_eq_right.mpr hCM]
          exact CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hCM hMN) hQ
      hyp14₁ := fun _ => h11.1
      hyp14₂ := fun _ => h11.2
      central := fun _ => CentralizersUnique.inv hcu }

theorem WeakClosureSetting.hyp6H {D : Data G} {V₀ V : Subgroup G}
    (h : WeakClosureSetting D V₀ V) : Hyp6H D.M V₀ V := by
  exact ⟨h.pair.elemAbelian, h.normalizer_eq, h.pair.le, h.pair.le_normalizer₀,
    fun hV₀ => (h.ti₀ hV₀).2, fun hV₀ => (h.ti₀ hV₀).1, h.normalizer₀,
    fun hV₀ v hv hv0 => (h.gen hV₀ v hv hv0).symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
