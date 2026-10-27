module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSignalizer
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section General

variable {G : Type} [Group G]

theorem commutator_self_eq_of_commutator_eq_top {H : Subgroup G} (h : commutator ↥H = ⊤) :
    ⁅H, H⁆ = H := by
  rw [← Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem commutator_map_conj_self {H : Subgroup G} (h : ⁅H, H⁆ = H) (g : G) :
    ⁅H.map (MulAut.conj g).toMonoidHom, H.map (MulAut.conj g).toMonoidHom⁆ =
      H.map (MulAut.conj g).toMonoidHom := by
  rw [← Subgroup.map_commutator, h]

theorem mem_normalizer_map_conj_inv_of_conj_mem {H : Subgroup G} {y δ : G}
    (h : y * δ * y⁻¹ ∈ Subgroup.normalizer (H : Set G)) :
    δ ∈ Subgroup.normalizer ((H.map (MulAut.conj y⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj] at h ⊢
  calc (H.map (MulAut.conj y⁻¹).toMonoidHom).map (MulAut.conj δ).toMonoidHom
      = (H.map (MulAut.conj (y * δ * y⁻¹)).toMonoidHom).map (MulAut.conj y⁻¹).toMonoidHom := by
        rw [map_conj_map_conj, map_conj_map_conj]
        congr 2
        group
    _ = H.map (MulAut.conj y⁻¹).toMonoidHom := by rw [h]

theorem map_conj_le_centralizer {D J : Subgroup G} (hDJ : D ≤ Subgroup.centralizer (J : Set G))
    (h : G) : D.map (MulAut.conj h).toMonoidHom ≤
      Subgroup.centralizer ((J.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) := by
  rintro _ ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨j, hj, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp (hDJ hδ) j hj
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc h * j * h⁻¹ * (h * δ * h⁻¹) = h * (j * δ) * h⁻¹ := by group
    _ = h * (δ * j) * h⁻¹ := by rw [hc]
    _ = h * δ * h⁻¹ * (h * j * h⁻¹) := by group

variable [Finite G]

theorem two_dvd_card_of_isQuasisimple {J : Subgroup G} (hJ : CFSG.Assembly.IsQuasisimple ↥J) :
    2 ∣ Nat.card J := by
  by_contra h2
  have hodd : Odd (Nat.card J) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hsol : Group.IsSolvable ↥J := CFSG.Milestones.odd_order_solvable hodd
  obtain ⟨k, hk⟩ := (Group.isSolvable_def ↥J).mp hsol
  have htop : ∀ m : ℕ, derivedSeries ↥J m = ⊤ := by
    intro m
    induction m with
    | zero => exact derivedSeries_zero _
    | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, hJ.1]
  have hbot : (⊤ : Subgroup ↥J) = ⊥ := by rw [← htop k, hk]
  have h1 : ∀ a : ↥J, a = 1 := fun a => by
    have : a ∈ (⊤ : Subgroup ↥J) := Subgroup.mem_top a
    rwa [hbot, Subgroup.mem_bot] at this
  obtain ⟨u, v, huv⟩ := hJ.2.toNontrivial.exists_pair_ne
  apply huv
  induction u using QuotientGroup.induction_on with
  | H a =>
    induction v using QuotientGroup.induction_on with
    | H b => rw [h1 a, h1 b]

theorem two_dvd_card_of_isComponentOf {J H : Subgroup G} (hJ : IsComponentOf J H) :
    2 ∣ Nat.card J :=
  two_dvd_card_of_isQuasisimple hJ.2.2

theorem mem_normalizer_of_conj_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G₀ D J : Subgroup G}
    (hS : ∀ K : Subgroup G, K ≤ Subgroup.normalizer (G₀ : Set G) → ⁅K, K⁆ = K → K ≤ G₀)
    (hT : ∀ E : Subgroup G, IsPGroup p E → E ≤ Subgroup.normalizer (G₀ : Set G) →
      ∀ T : Subgroup G, T ≤ G₀ → T ≠ ⊥ → IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set G) →
        ∃ Q₁ Q₂ : Subgroup G, Q₁ ≤ G₀ ∧ Q₂ ≤ G₀ ∧ IsPGroup 2 Q₁ ∧ IsPGroup 2 Q₂ ∧
          E ≤ Subgroup.normalizer (Q₁ : Set G) ∧ E ≤ Subgroup.normalizer (Q₂ : Set G) ∧
          Q₁ ⊔ Q₂ = G₀)
    (hsig : ∀ Q : Subgroup G, D ≤ Subgroup.normalizer (Q : Set G) →
      Nat.Coprime p (Nat.card Q) → Q ≤ Subgroup.normalizer (G₀ : Set G))
    (hG₀ : ⁅G₀, G₀⁆ = G₀) (hJ : ⁅J, J⁆ = J) (hJ2 : 2 ∣ Nat.card J) (hDp : IsPGroup p D)
    (hDJ : D ≤ Subgroup.centralizer (J : Set G)) {h : G}
    (hJh : J.map (MulAut.conj h).toMonoidHom ≤ Subgroup.normalizer (G₀ : Set G))
    (hDh : D.map (MulAut.conj h).toMonoidHom ≤ Subgroup.normalizer (G₀ : Set G)) :
    h ∈ Subgroup.normalizer (G₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := J.map (MulAut.conj h).toMonoidHom with hK
  set E := D.map (MulAut.conj h).toMonoidHom with hE
  have hKG₀ : K ≤ G₀ := hS K hJh (commutator_map_conj_self hJ h)
  have hK2 : 2 ∣ Nat.card K := by
    rw [hK, Subgroup.card_map_of_injective (MulAut.conj h).injective]
    exact hJ2
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 hK2
  set T := Subgroup.zpowers (t : G) with hTdef
  have hot : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have hTK : T ≤ K := Subgroup.zpowers_le.mpr t.2
  have hTne : T ≠ ⊥ := by
    intro hbot
    have h1 : (t : G) = 1 := by
      have : (t : G) ∈ T := Subgroup.mem_zpowers _
      rwa [hbot, Subgroup.mem_bot] at this
    rw [h1, orderOf_one] at hot
    exact absurd hot (by norm_num)
  have hTp : IsPGroup 2 T :=
    IsPGroup.of_card (n := 1) (by rw [hTdef, Nat.card_zpowers, hot, pow_one])
  have hEC : E ≤ Subgroup.centralizer (K : Set G) := map_conj_le_centralizer hDJ h
  have hET : E ≤ Subgroup.normalizer (T : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer (T : Set G) (Subgroup.centralizer_le hTK (hEC he))
  obtain ⟨Q₁, Q₂, -, -, hQ₁p, hQ₂p, hEQ₁, hEQ₂, hQ⟩ :=
    hT E (hDp.map _) hDh T (hTK.trans hKG₀) hTne hTp hET
  have hsig' : ∀ Q : Subgroup G, IsPGroup 2 Q → E ≤ Subgroup.normalizer (Q : Set G) →
      Q.map (MulAut.conj h⁻¹).toMonoidHom ≤ Subgroup.normalizer (G₀ : Set G) := by
    intro Q hQp hEQ
    refine hsig _ (fun δ hδ => mem_normalizer_map_conj_inv_of_conj_mem
      (hEQ ⟨δ, hδ, rfl⟩)) ?_
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hG₀' : G₀.map (MulAut.conj h⁻¹).toMonoidHom ≤ Subgroup.normalizer (G₀ : Set G) := by
    have h12 := sup_le (hsig' Q₁ hQ₁p hEQ₁) (hsig' Q₂ hQ₂p hEQ₂)
    rwa [← Subgroup.map_sup, hQ] at h12
  have hle : G₀.map (MulAut.conj h⁻¹).toMonoidHom ≤ G₀ :=
    hS _ hG₀' (commutator_map_conj_self hG₀ h⁻¹)
  have heq : G₀.map (MulAut.conj h⁻¹).toMonoidHom = G₀ :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).ge
  have hinv : h⁻¹ ∈ Subgroup.normalizer (G₀ : Set G) := mem_normalizer_iff_map_conj.mpr heq
  simpa using Subgroup.inv_mem _ hinv

omit [Finite G] in
theorem normalizer_le_of_conj_le {M D J K X : Subgroup G}
    (h69 : ∀ h : G, J.map (MulAut.conj h).toMonoidHom ≤ M →
      D.map (MulAut.conj h).toMonoidHom ≤ M → h ∈ M)
    (hJX : J ≤ X) (hDX : D ≤ X) (hXM : X ≤ M)
    (hN : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    Subgroup.normalizer (K : Set G) ≤ M := by
  intro n hn
  have hX : X.map (MulAut.conj n).toMonoidHom = X := map_conj_eq_of_mem_normalizer (hN hn)
  refine h69 n ?_ ?_
  · calc J.map (MulAut.conj n).toMonoidHom ≤ X.map (MulAut.conj n).toMonoidHom :=
          Subgroup.map_mono hJX
      _ = X := hX
      _ ≤ M := hXM
  · calc D.map (MulAut.conj n).toMonoidHom ≤ X.map (MulAut.conj n).toMonoidHom :=
          Subgroup.map_mono hDX
      _ = X := hX
      _ ≤ M := hXM

theorem centralizer_le_of_conj_le {M D J K : Subgroup G} {d : G}
    (h69 : ∀ h : G, J.map (MulAut.conj h).toMonoidHom ≤ M →
      D.map (MulAut.conj h).toMonoidHom ≤ M → h ∈ M)
    (hK : IsComponentOf K (Subgroup.centralizer {d})) (hJK : J ≤ K)
    (hJd : J ≤ Subgroup.centralizer {d}) (hDd : D ≤ Subgroup.centralizer {d})
    (hDcomp : ∀ K' : Subgroup G, IsComponentOf K' (Subgroup.centralizer {d}) →
      D ≤ Subgroup.normalizer (K' : Set G))
    (hNK : Subgroup.normalizer (K : Set G) ≤ M) :
    Subgroup.centralizer {d} ≤ M := by
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set V : Subgroup G := C ⊓ ⨅ (K' : Subgroup G) (_ : IsComponentOf K' C),
    Subgroup.normalizer (K' : Set G) with hV
  have hmemV : ∀ v, v ∈ V ↔
      v ∈ C ∧ ∀ K' : Subgroup G, IsComponentOf K' C → v ∈ Subgroup.normalizer (K' : Set G) := by
    intro v
    simp only [hV, Subgroup.mem_inf, Subgroup.mem_iInf]
  have hJV : J ≤ V := by
    intro j hj
    refine (hmemV j).mpr ⟨hJd hj, fun K' hK' => ?_⟩
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK hK' with heq | hcomm
    · rw [← heq]
      exact Subgroup.le_normalizer (hJK hj)
    · have hKC : K ≤ Subgroup.centralizer (K' : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact Subgroup.centralizer_le_normalizer (K' : Set G) (hKC (hJK hj))
  have hDV : D ≤ V := fun δ hδ => (hmemV δ).mpr ⟨hDd hδ, fun K' hK' => hDcomp K' hK' hδ⟩
  have hVM : V ≤ M := fun v hv => hNK (((hmemV v).mp hv).2 K hK)
  have hconjV : ∀ c ∈ C, V.map (MulAut.conj c).toMonoidHom ≤ V := by
    intro c hc
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨hvC, hvN⟩ := (hmemV v).mp hv
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine (hmemV _).mpr ⟨C.mul_mem (C.mul_mem hc hvC) (C.inv_mem hc), fun K' hK' => ?_⟩
    have hK'' : IsComponentOf (K'.map (MulAut.conj c⁻¹).toMonoidHom) C := by
      have := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hK' c⁻¹
      rwa [map_conj_eq_of_mem (C.inv_mem hc)] at this
    exact conj_mem_normalizer_of_mem_normalizer_map (hvN _ hK'')
  intro c hc
  exact h69 c ((Subgroup.map_mono hJV).trans ((hconjV c hc).trans hVM))
    ((Subgroup.map_mono hDV).trans ((hconjV c hc).trans hVM))

end General

section Ctx

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.presents (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    GGPresentsG0 (ggG0 p B x L D J) Δ t n f ψ :=
  ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1.1, h.2.2.2.2.2.1.2⟩

theorem GGSixCtxV2.j_comp (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
  h.stdSub.1.2.2.2.2.2.1

theorem GGSixCtxV2.two_dvd_card_j (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    2 ∣ Nat.card J :=
  two_dvd_card_of_isComponentOf h.j_comp

theorem GGSixCtxV2.d_le_centralizer (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {d : G}
    (hd : d ∈ D) : D ≤ Subgroup.centralizer {d} := fun δ hδ =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (h.d_elem.1.is_comm.comm (⟨δ, hδ⟩ : ↥D) ⟨d, hd⟩))

theorem GGSixCtxV2.normalizer_ggKd_le (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (h69 : ∀ g : G, J.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J →
      D.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J → g ∈ ggM p B x L D J)
    (h66 : Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J) {d : G} (hd : d ∈ D)
    (hX : Subgroup.normalizer (ggKd p B x L D J d : Set G) ≤
      Subgroup.normalizer ((Bs ⊔ ggKd p B x L D J d ⊔
        Subgroup.centralizer (ggKd p B x L D J d : Set G) : Subgroup G) : Set G)) :
    Subgroup.normalizer (ggKd p B x L D J d : Set G) ≤ ggM p B x L D J := by
  have hKM := h.ggKd_sup_centralizer_le h66 hd
  refine normalizer_le_of_conj_le h69 ((le_ggKd p B x L D J d).trans
    (le_sup_right.trans le_sup_left)) (h.d_le_bstar.trans (le_sup_left.trans le_sup_left)) ?_ hX
  exact sup_le (sup_le h.bstar_le_normalizer (le_sup_left.trans hKM)) (le_sup_right.trans hKM)

theorem GGSixCtxV2.centralizer_le_ggM (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (h69 : ∀ g : G, J.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J →
      D.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J → g ∈ ggM p B x L D J)
    {d : G} (hd : d ∈ D)
    (h65 : IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}))
    (h68 : ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {d}) →
      D ≤ Subgroup.normalizer (K : Set G))
    (h69ii : Subgroup.normalizer (ggKd p B x L D J d : Set G) ≤ ggM p B x L D J) :
    Subgroup.centralizer {d} ≤ ggM p B x L D J :=
  centralizer_le_of_conj_le h69 h65 (le_ggKd p B x L D J d) ((h.le_ggG0_inf hd).trans inf_le_right)
    (h.d_le_centralizer hd) h68 h69ii

end Ctx

section CtxU

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}

theorem GGSixCtxV2.mem_of_conj_le (hS : GGSchreierPerfectInput) (hT : GGTwoSignalizerGenInput)
    (h : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hodd : Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))))
    (hsig : ∀ Q : Subgroup G, D ≤ Subgroup.normalizer (Q : Set G) →
      Nat.Coprime p (Nat.card Q) → Q ≤ ggM p B x L D J)
    {g : G} (hJg : J.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J)
    (hDg : D.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J) : g ∈ ggM p B x L D J := by
  have hDp : IsPGroup p D := fun e => ⟨1, Subtype.ext (by simpa using h.d_elem.2 e e.2)⟩
  exact mem_normalizer_of_conj_le h.prime h.ne_two (hS G t n f ψ _ h.presents hodd)
    (hT G t n f ψ _ h.presents p h.prime h.ne_two) hsig
    (commutator_self_eq_of_commutator_eq_top h.perfect)
    (commutator_self_eq_of_commutator_eq_top h.j_comp.2.2.1) h.two_dvd_card_j hDp
    h.le_centralizer_J hJg hDg

end CtxU

end CFSG.StandardType
