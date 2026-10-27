module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoRestAutK
import CFSG.Quasithin.SteinbergCBAlternatingAut
import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Rank

theorem ggAKF_card_le_of_unique {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P Bs A : Subgroup G} (hBs : IsElemAbelian p Bs) (hBs1 : Bs ≠ ⊥)
    (huniq : ∀ E : Subgroup G, E ≤ P → IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs)
    (hA : IsElemAbelian p A) (hAP : A ≤ P) : Nat.card A ≤ Nat.card Bs := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  rw [not_le] at hlt
  have hpg : ∀ {X : Subgroup G}, IsElemAbelian p X → IsPGroup p X := fun hX y =>
    ⟨1, Subtype.ext (by simpa using hX.2 y y.2)⟩
  obtain ⟨k, hk⟩ := (hpg hBs).exists_card_eq
  obtain ⟨a, ha⟩ := (hpg hA).exists_card_eq
  have hAB : ¬ A ≤ Bs := fun h => absurd (Subgroup.card_le_of_le h) (not_le.mpr hlt)
  obtain ⟨v, hvA, hvB⟩ := IsConcreteLE.not_le_iff_exists.mp hAB
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hBs1 (Subgroup.eq_bot_of_card_eq Bs hk)
  have hka : k ≤ a := by
    have h := hlt.le
    rw [hk, ha] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  have hdvd1 : Nat.card (Subgroup.zpowers v) ∣ p ^ k := by
    rw [Nat.card_zpowers]
    exact (orderOf_dvd_of_pow_eq_one (hA.2 v hvA)).trans (dvd_pow_self p hk0)
  have hdvd2 : p ^ k ∣ Nat.card A := by
    rw [ha]
    exact Nat.pow_dvd_pow p hka
  obtain ⟨K, hKcard, hvK, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp hdvd1 hdvd2
    (Subgroup.zpowers_le.mpr hvA)
  have hKel : IsElemAbelian p K := by
    have := hA.1
    refine ⟨⟨⟨fun c d => ?_⟩⟩, fun w hw => hA.2 w (hKA hw)⟩
    apply Subtype.ext
    have h := congrArg Subtype.val (mul_comm' (⟨c, hKA c.2⟩ : A) ⟨d, hKA d.2⟩)
    simpa using h
  have hK := huniq K (hKA.trans hAP) hKel (by rw [hKcard, hk])
  exact hvB (hK ▸ hvK (Subgroup.mem_zpowers v))

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggAKF_card_le_card_bstar (hp : p.Prime) (hBs : IsElemAbelian p Bs) (hBs1 : Bs ≠ ⊥)
    (h1 : GGSixStepOne p B Bs x L D J) {E : Subgroup G} (hE : IsElemAbelian p E)
    (hEM : E ≤ ggM p B x L D J) : Nat.card E ≤ Nat.card Bs := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, -, huniq⟩ := h1.2.2.2.1
  have hpg : ∀ {X : Subgroup G}, IsElemAbelian p X → IsPGroup p X := fun hX y =>
    ⟨1, Subtype.ext (by simpa using hX.2 y y.2)⟩
  obtain ⟨R, hR⟩ := ((hpg hE).comap_of_injective (ggM p B x L D J).subtype
    (ggM p B x L D J).subtype_injective).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ggM p B x L D J) R P
  have hEP : E.map (MulAut.conj (g : G)).toMonoidHom ≤
      (P : Subgroup (ggM p B x L D J)).map (ggM p B x L D J).subtype := by
    rintro _ ⟨e, he, rfl⟩
    have hmem : MulAut.conj g (⟨e, hEM he⟩ : ggM p B x L D J) ∈
        ((g • R : Sylow p (ggM p B x L D J)) : Subgroup (ggM p B x L D J)) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hR (show (⟨e, hEM he⟩ : ggM p B x L D J) ∈
        E.comap (ggM p B x L D J).subtype from he))
    rw [hg] at hmem
    exact ⟨_, hmem, rfl⟩
  have h := ggAKF_card_le_of_unique hp hBs hBs1 huniq (isElemAbelian_map_hom hE _) hEP
  rwa [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective] at h

end Rank

section Central

theorem ggAKF_eq_of_mem_center {L : Type*} [Group L] (hL : commutator L = ⊤) (φ : L →* L)
    (hφ : ∀ l : L, l⁻¹ * φ l ∈ Subgroup.center L) (l : L) : φ l = l := by
  let δ : L →* L := MonoidHom.mk' (fun l => l⁻¹ * φ l) (fun a b => by
    have hc : ∀ g : L, g * (a⁻¹ * φ a) = (a⁻¹ * φ a) * g := fun g =>
      Subgroup.mem_center_iff.mp (hφ a) g
    show (a * b)⁻¹ * φ (a * b) = a⁻¹ * φ a * (b⁻¹ * φ b)
    rw [map_mul, mul_inv_rev]
    calc b⁻¹ * a⁻¹ * (φ a * φ b) = b⁻¹ * (a⁻¹ * φ a) * φ b := by group
      _ = (a⁻¹ * φ a) * b⁻¹ * φ b := by rw [hc b⁻¹]
      _ = a⁻¹ * φ a * (b⁻¹ * φ b) := by group)
  have hker : commutator L ≤ δ.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨c, d, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp (hφ d) (δ c)
  have hl : δ l = 1 := hker (hL ▸ Subgroup.mem_top l)
  exact (inv_mul_eq_one.mp hl).symm

end Central

section AltFive

theorem ggAKF_card_le_five_mul {G : Type} [Group G] [Finite G] {A L₁ : Subgroup G}
    (hA : IsPGroup 5 A) (hAN : A ≤ Subgroup.normalizer (L₁ : Set G)) (hL : commutator ↥L₁ = ⊤)
    (e : ↥L₁ ⧸ Subgroup.center ↥L₁ ≃* alternatingGroup (Fin 5)) :
    Nat.card A ≤ 5 * Nat.card (A ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hNn : (L₁.subgroupOf (Subgroup.normalizer (L₁ : Set G))).Normal :=
    Subgroup.normal_in_normalizer
  let iso : ↥(L₁.subgroupOf (Subgroup.normalizer (L₁ : Set G))) ≃* ↥L₁ :=
    Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  let ρ : ↥(Subgroup.normalizer (L₁ : Set G)) →* MulAut ↥L₁ :=
    (MulAut.congr iso).toMonoidHom.comp MulAut.conjNormal
  have hρ : ∀ (g : ↥(Subgroup.normalizer (L₁ : Set G))) (l : ↥L₁),
      ((ρ g l : ↥L₁) : G) = (g : G) * l * (g : G)⁻¹ := by
    intro g l
    have h1 := congrArg Subtype.val (MulAut.conjNormal_apply
      (H := L₁.subgroupOf (Subgroup.normalizer (L₁ : Set G))) g (iso.symm l))
    simp [ρ, iso]
  let q := CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (Subgroup.center ↥L₁)
  let c : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective (CFSG.Quasithin.SteinbergCB.conjPerm 5)
      ⟨CFSG.Quasithin.SteinbergCB.conjPerm_injective (by norm_num),
        CFSG.Quasithin.SteinbergCB.conjPerm_surjective (Or.inl rfl)⟩
  let σ : ↥A →* Equiv.Perm (Fin 5) := c.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp
    (q.comp (ρ.comp (Subgroup.inclusion hAN))))
  have hrange : Nat.card σ.range ≤ 5 := by
    have hp : IsPGroup 5 σ.range := hA.of_surjective σ.rangeRestrict σ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hdvd : 5 ^ k ∣ 120 := by
      rw [← hk]
      have h := Subgroup.card_subgroup_dvd_card σ.range
      rw [Nat.card_perm, Nat.card_fin] at h
      exact h
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have h25 : 5 ^ 2 ∣ 5 ^ k := Nat.pow_dvd_pow 5 (by omega)
      have := h25.trans hdvd
      norm_num at this
    rw [hk]
    calc 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 5 := by norm_num
  have hker : ∀ a : ↥A, σ a = 1 → (a : G) ∈ Subgroup.centralizer (L₁ : Set G) := by
    intro a ha
    have h1 : q (ρ (Subgroup.inclusion hAN a)) = 1 := by
      have h' : (MulAut.congr e) (q (ρ (Subgroup.inclusion hAN a))) = 1 := by
        have h0 := congrArg c ha
        simpa [σ] using h0
      exact (MulAut.congr e).injective (h'.trans (map_one _).symm)
    have h2 : ∀ l : ↥L₁, l⁻¹ * ρ (Subgroup.inclusion hAN a) l ∈ Subgroup.center ↥L₁ := by
      intro l
      have h3 := congrArg (fun φ : MulAut (↥L₁ ⧸ Subgroup.center ↥L₁) =>
        φ (QuotientGroup.mk' (Subgroup.center ↥L₁) l)) h1
      simp only [MulAut.one_apply] at h3
      rw [CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply] at h3
      exact QuotientGroup.eq.mp h3.symm
    have h5 := ggAKF_eq_of_mem_center hL (ρ (Subgroup.inclusion hAN a)).toMonoidHom h2
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h6 : ((ρ (Subgroup.inclusion hAN a) ⟨l, hl⟩ : ↥L₁) : G) = l :=
      congrArg Subtype.val (h5 ⟨l, hl⟩)
    rw [hρ] at h6
    simp only [Subgroup.coe_inclusion] at h6
    calc l * (a : G) = ((a : G) * l * (a : G)⁻¹) * a := by rw [h6]
      _ = a * l := by group
  have hkercard : Nat.card σ.ker ≤
      Nat.card (A ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : ↥A) : G),
      Subgroup.mem_inf.mpr ⟨(k : ↥A).2, hker k (MonoidHom.mem_ker.mp k.2)⟩⟩) ?_
    intro k₁ k₂ h
    have h' : ((k₁ : ↥A) : G) = ((k₂ : ↥A) : G) :=
      congrArg (fun z : ↥(A ⊓ Subgroup.centralizer (L₁ : Set G)) => (z : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hcardA : Nat.card A = Nat.card σ.range * Nat.card σ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange σ).toEquiv]
  rw [hcardA]
  exact Nat.mul_le_mul hrange hkercard

end AltFive

section Coprime

theorem ggAKF_exists_noncentral_coprime {L : Type*} [Group L] [Finite L]
    (hL : CFSG.Assembly.IsQuasisimple L) {p : ℕ} (hp : p.Prime) :
    ∃ g : L, g ∉ Subgroup.center L ∧ Nat.Coprime (orderOf g) p := by
  have : Fact p.Prime := ⟨hp⟩
  have := hL.2
  by_contra hcon
  have hall : ∀ g : L, Nat.Coprime (orderOf g) p → g ∈ Subgroup.center L := fun g hg => by
    by_contra hgz
    exact hcon ⟨g, hgz, hg⟩
  have hpQ : IsPGroup p (L ⧸ Subgroup.center L) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨e, n', hn', he⟩ :=
        Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' p hp.one_lt.ne'
      refine ⟨e, ?_⟩
      have hcop : Nat.Coprime (orderOf (g ^ p ^ e)) p := by
        rw [orderOf_pow_of_dvd (pow_ne_zero e hp.ne_zero) ⟨n', he⟩, he,
          Nat.mul_div_cancel_left _ (pow_pos hp.pos e)]
        exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn').symm
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hall _ hcop
  have hZ : Subgroup.center (L ⧸ Subgroup.center L) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (L ⧸ Subgroup.center L)) with h | h
    · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).mp hpQ.center_nontrivial)
    · exact h
  have hcomm : commutator L ≤ Subgroup.center L := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨c, d, rfl⟩
    rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
    have hcd : (c : L ⧸ Subgroup.center L) * (d : L ⧸ Subgroup.center L) =
        (d : L ⧸ Subgroup.center L) * (c : L ⧸ Subgroup.center L) :=
      Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top (d : L ⧸ Subgroup.center L)) _
    have h1 := map_commutatorElement (QuotientGroup.mk' (Subgroup.center L)) c d
    simp only [QuotientGroup.mk'_apply] at h1
    rw [h1, commutatorElement_eq_one_iff_mul_comm]
    exact hcd
  have htop : Subgroup.center L = ⊤ := by
    rw [eq_top_iff, ← hL.1]
    exact hcomm
  obtain ⟨y, hy⟩ := exists_ne (1 : L ⧸ Subgroup.center L)
  induction y using QuotientGroup.induction_on with
  | H g =>
    apply hy
    rw [QuotientGroup.eq_one_iff, htop]
    exact Subgroup.mem_top g

theorem ggAKF_exists_noncentral_coprime_mem {G : Type*} [Group G] [Finite G] {L₁ : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple ↥L₁) {p : ℕ} (hp : p.Prime) :
    ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧ Nat.Coprime (orderOf g) p := by
  obtain ⟨g, hgz, hg⟩ := ggAKF_exists_noncentral_coprime hL hp
  rw [Subgroup.mem_center_iff] at hgz
  obtain ⟨l, hl⟩ := not_forall.mp hgz
  refine ⟨g, g.2, ⟨l, l.2, fun h => hl (Subtype.ext h.symm)⟩, ?_⟩
  rwa [Subgroup.orderOf_coe]

end Coprime

end CFSG.StandardType
