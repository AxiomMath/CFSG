module

public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualTransv
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVICoord
public import CFSG.RankThree.GF2n.Stroth80.Sec34Wc

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z X B : Subgroup G}

theorem caseVIClosure_of_coord {n : ℕ} (hcB : Ctx M Q Z B) (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) {S : Subgroup G} (hSH : S ≤ H0 M Z)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφQ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) (e : M₀.E), M₀.Qf (φ m e) = M₀.Qf e)
    {F : Type} [Field F] [Finite F]
    (ρ' : ↥S →* GL (Fin n) F) (hrange : ρ'.range = StatedSL n F)
    (hker : ρ'.ker = Q.subgroupOf S)
    (C : NatDualCoord (φ.comp (Subgroup.inclusion hSH)) ρ') :
    LB M Q B ⊓ S ≤ Q := by
  by_contra hnot
  obtain ⟨a₀, ha₀, ha₀Q⟩ := SetLike.not_le_iff_exists.mp hnot
  have hSM : S ≤ M := fun x hx => (hSH hx).1
  set ρ : ↥S →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hSH) with hρ
  have hn3 : 3 ≤ n := hn
  have hq4 : 4 ≤ Nat.card Z := hcB.hyp.q4
  have hcard : Nat.card K = Nat.card Z := h.card
  have hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 :=
    exists_ne_zero_sq_ne_one_of_two_lt_card K (by rw [hcard]; omega)
  haveI : CharP F 2 := charP_of_injective_ringHom C.θ₁.toRingHom.injective 2
  let Qd : QuadDatum K M₀.E := quadDatumOfModel M₀
  have hQρ : ∀ (g : ↥S) (e : M₀.E), Qd.Qf (ρ g e) = Qd.Qf e := fun g e => hφiso _ e
  have hZQ : Z ≤ Q := hcB.Z_le_Q
  obtain ⟨b, hb0, hbs, hB, -, -⟩ := hcB.dictB h
  let N : Subgroup ↥S := (LB M Q B).subgroupOf S
  have hmemN : ∀ a : ↥S, a ∈ N ↔ (a : G) ∈ LB M Q B := fun a => Iff.rfl
  have hN2 : ∀ a ∈ N, ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((ρ' a : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    intro a ha
    have h1 : a ^ 2 ∈ ρ'.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hcB.sq_mem_Q_of_mem_LB ((hmemN a).mp ha)
    have h2 : ρ' (a ^ 2) = 1 := h1
    rw [pow_two, map_mul] at h2
    have := congrArg Units.val h2
    simpa using this
  have hNs : ∀ s : ↥S, ρ s b = b → ∀ a ∈ N, s * a * s⁻¹ ∈ N := by
    intro s hsb a ha
    have hsM' : (s : G) ∈ M := hSM s.2
    have hle' : B ⊔ Z ≤ M₀.lift (M₀.img B) := sup_le
      (fun u hu => ⟨hcB.le hu, M₀.pi_mem_img hu (hcB.le hu)⟩)
      (fun z hz => ⟨hZQ hz, by
        rw [(M₀.π_ker z (hZQ hz)).mpr hz]; exact AddSubgroup.zero_mem _⟩)
    have hsn : (s : G) ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      have hxQ : x ∈ Q := (hle' hx).1
      obtain ⟨t, ht⟩ := (hB _).mp (hle' hx).2
      have hsxQ : (s : G) * x * (s : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hcB.hyp.Q_normal.2 hsM') x).mp hxQ
      have hπ : M₀.π ((s : G) * x * (s : G)⁻¹) = t • b := by
        have := hφπ ⟨s, hSH s.2⟩ x hxQ
        rw [this]
        show ρ s (M₀.π x) = t • b
        rw [ht, map_smul, hsb]
      have hmem : M₀.π ((s : G) * x * (s : G)⁻¹) ∈ M₀.img (B ⊔ Z) :=
        M₀.img_mono le_sup_left ((hB _).mpr ⟨t, hπ⟩)
      exact (M₀.mem_img_iff le_sup_right hsxQ).mp hmem
    have hsL : (s : G) ∈ Subgroup.normalizer ((LB M Q B : Subgroup G) : Set G) :=
      ((hcB.mem_normalizer_LB_iff' hw hn hno hsM').mpr hsn)
    rw [hmemN] at ha ⊢
    have h1 : (s : G) * (a : G) * (s : G)⁻¹ ∈ LB M Q B :=
      (Subgroup.mem_normalizer_iff.mp hsL _).mp ha
    simpa using h1
  have ha₀N : (⟨a₀, ha₀.2⟩ : ↥S) ∈ N := ha₀.1
  have ha₀1 : ρ' ⟨a₀, ha₀.2⟩ ≠ 1 := by
    intro h1
    have : (⟨a₀, ha₀.2⟩ : ↥S) ∈ ρ'.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at this
    exact ha₀Q this
  obtain ⟨a, haN, c, γ', hc, hγ, hγc, ha⟩ :=
    C.exists_transvection_of_normal Qd hn3 hrange hQρ hK b hbs N hN2 hNs ha₀N ha₀1
  obtain ⟨hne1, hsing, hrk⟩ := C.transvection_range Qd hn3 hrange hQρ hK a c γ' hc hγ hγc ha
  have haLB : (a : G) ∈ LB M Q B := (hmemN a).mp haN
  have haH : (a : G) ∈ H0 M Z := hSH a.2
  have haM : (a : G) ∈ M := haH.1
  have hQn : ∀ x ∈ Q, (a : G) * x * (a : G)⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hcB.hyp.Q_normal.2 haM) x).mp hx
  have hQn' : ∀ x ∈ Q, (a : G)⁻¹ * x * (a : G) ∈ Q := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (hcB.hyp.Q_normal.2 (M.inv_mem haM)) x).mp hx
    simpa using this
  have hTπ : ∀ x ∈ Q, M₀.π ((a : G) * x * (a : G)⁻¹) = (φ ⟨a, haH⟩) (M₀.π x) :=
    fun x hx => hφπ ⟨a, haH⟩ x hx
  have hKcard : 1 < Nat.card K := by rw [hcard]; omega
  have hA2 := isA2_iff M₀ h.reg hcard hKcard (φ ⟨a, haH⟩) hQn hQn' hTπ
  have haQ : (a : G) ∉ Q := fun haQ' => hne1 ((hφQ ⟨a, haH⟩).mpr haQ')
  exact hno a haLB (hA2.mpr ⟨haQ, hcB.sq_mem_Q_of_mem_LB haLB, hrk, hsing⟩)

end CFSG.RankThree.GF2n.Stroth80
