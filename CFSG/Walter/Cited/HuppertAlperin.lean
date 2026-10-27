module

public import CFSG.Walter.Cited.HuppertBasic
public import CFSG.Walter.Cited.HuppertPlane
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_12_c

public section

namespace CFSG.Walter.Huppert

open scoped Pointwise commutatorElement

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

omit [Finite X] hp in
theorem mem_normalizer_sup {A B : Subgroup X} {g : X} (hA : g ∈ Subgroup.normalizer (A : Set X))
    (hB : g ∈ Subgroup.normalizer (B : Set X)) : g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup X) :
      Set X) := by
  have hmap : ∀ {H : Subgroup X}, g ∈ Subgroup.normalizer (H : Set X) →
      H.map (MulAut.conj g).toMonoidHom = H := by
    intro H hH
    ext x
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    rw [Subgroup.mem_normalizer_iff''] at hH
    exact (hH x).symm
  have hsup : (A ⊔ B).map (MulAut.conj g).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hmap hA, hmap hB]
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  have := congrArg (fun H : Subgroup X => x ∈ H) hsup
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at this
  exact (Iff.of_eq this).symm

omit [Finite X] hp in
theorem normalizer_le_normalizer_centralizer (Q : Subgroup X) :
    Subgroup.normalizer (Q : Set X) ≤
      Subgroup.normalizer ((Subgroup.centralizer (Q : Set X) : Subgroup X) : Set X) := by
  have key : ∀ {g c : X}, g ∈ Subgroup.normalizer (Q : Set X) →
      c ∈ Subgroup.centralizer (Q : Set X) → g * c * g⁻¹ ∈ Subgroup.centralizer (Q : Set X) := by
    intro g c hg hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff''.mp hg q).mp hq
      exact this
    have h := hc _ hq'
    calc q * (g * c * g⁻¹) = g * ((g⁻¹ * q * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * q * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * q := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact key hg
  · intro h
    have := key (Subgroup.inv_mem _ hg) h
    simpa [mul_assoc] using this

omit [Finite X] hp in
theorem mem_of_mem_sup_centralizer {Q P : Subgroup X} (hQP : Q ≤ P)
    (hcen : Subgroup.centralizer (Q : Set X) ⊓ P ≤ Q) {x : X} (hxP : x ∈ P)
    (hx : x ∈ Q ⊔ Subgroup.centralizer (Q : Set X)) : x ∈ Q := by
  have hQC : Q ≤ Subgroup.normalizer ((Subgroup.centralizer (Q : Set X) : Subgroup X) : Set X) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_centralizer Q)
  have hx' : x ∈ ((Q ⊔ Subgroup.centralizer (Q : Set X) : Subgroup X) : Set X) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q _ hQC] at hx'
  obtain ⟨q, hq, c, hc, rfl⟩ := hx'
  have hcP : c ∈ P := by
    have : c = q⁻¹ * (q * c) := by group
    rw [this]
    exact P.mul_mem (P.inv_mem (hQP hq)) hxP
  exact Q.mul_mem hq (hcen ⟨hc, hcP⟩)

theorem exists_mem_normalizer_not_mem {Q P : Subgroup X} (hP : IsPGroup p P) (hQP : Q ≤ P)
    (hne : Q ≠ P) : ∃ t ∈ P, t ∈ Subgroup.normalizer (Q : Set X) ∧ t ∉ Q := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt : Q.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    exact le_antisymm hQP (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := P) _ hlt
  obtain ⟨t, htN, htQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQP, Subgroup.mem_subgroupOf] at htN
  exact ⟨t, t.2, htN, fun h => htQ (Subgroup.mem_subgroupOf.mpr h)⟩

theorem exists_conj_eq {R T T₂ : Subgroup X} (hTR : T ≤ R) (hT₂R : T₂ ≤ R) (hT : IsPGroup p T)
    (hT₂ : IsPGroup p T₂) (hidx : ¬ p ∣ T.relIndex R) (hcard : Nat.card T₂ = Nat.card T) :
    ∃ r ∈ R, T₂ = T.map (MulAut.conj r).toMonoidHom := by
  have hT' : IsPGroup p (T.subgroupOf R) :=
    hT.of_injective (Subgroup.subgroupOfEquivOfLe hTR).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTR).injective
  have hT₂' : IsPGroup p (T₂.subgroupOf R) :=
    hT₂.of_injective (Subgroup.subgroupOfEquivOfLe hT₂R).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hT₂R).injective
  have hidx₂ : ¬ p ∣ (T₂.subgroupOf R).index := by
    have h1 := (T.subgroupOf R).card_mul_index
    have h2 := (T₂.subgroupOf R).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv] at h1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₂R).toEquiv, hcard] at h2
    have hpos : 0 < Nat.card T := Nat.card_pos
    have : (T₂.subgroupOf R).index = T.relIndex R := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [h2, Subgroup.relIndex, h1]
    rw [this]
    exact hidx
  let S₁ : Sylow p R := hT'.toSylow hidx
  let S₂ : Sylow p R := hT₂'.toSylow hidx₂
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq R S₁ S₂
  refine ⟨y, y.2, ?_⟩
  ext x
  constructor
  · intro hx
    have hxS₂ : (⟨x, hT₂R hx⟩ : R) ∈ (S₂ : Subgroup R) := Subgroup.mem_subgroupOf.mpr hx
    rw [← hy, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS₂
    have h := Subgroup.mem_subgroupOf.mp hxS₂
    refine ⟨y⁻¹ * x * y, ?_, ?_⟩
    · simpa [MulAut.smul_def, MulAut.conj_apply] using h
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨z, hz, rfl⟩
    have hzR : z ∈ R := hTR hz
    have hmem : (⟨z, hzR⟩ : R) ∈ (S₁ : Subgroup R) := Subgroup.mem_subgroupOf.mpr hz
    have hmem₂ : y * ⟨z, hzR⟩ * y⁻¹ ∈ (S₂ : Subgroup R) := by
      rw [← hy, Sylow.coe_subgroup_smul]
      exact ⟨⟨z, hzR⟩, hmem, rfl⟩
    have := Subgroup.mem_subgroupOf.mp hmem₂
    simpa [MulAut.conj_apply] using this

@[expose] noncomputable def frattiniAction (Q : Subgroup X) :
    Subgroup.normalizer (Q : Set X) →* MulAut (Q ⧸ frattini Q) :=
  (frattiniAut Q).comp Q.normalizerMonoidHom

omit [Finite X] hp in
theorem frattiniAction_mk (Q : Subgroup X) (n : Subgroup.normalizer (Q : Set X)) (x : Q) :
    frattiniAction Q n (x : Q ⧸ frattini Q) = ((Q.normalizerMonoidHom n x : Q) : Q ⧸ frattini Q) :=
  frattiniAut_mk _ x

theorem frattiniAction_eq_one {Q : Subgroup X} (hQ : IsPGroup p Q)
    {n : Subgroup.normalizer (Q : Set X)} (hn : (n : X) ∈ Q ⊔ Subgroup.centralizer (Q : Set X)) :
    frattiniAction Q n = 1 := by
  have hker : Q ⊔ Subgroup.centralizer (Q : Set X) ≤
      (frattiniAction Q).ker.map (Subgroup.normalizer (Q : Set X)).subtype := by
    refine sup_le (fun q hq => ⟨⟨q, Subgroup.le_normalizer hq⟩, ?_, rfl⟩)
      (fun c hc => ⟨⟨c, Subgroup.centralizer_le_normalizer _ hc⟩, ?_, rfl⟩)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker]
      ext v
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
      rw [frattiniAction_mk, MulAut.one_apply, QuotientGroup.eq]
      have hcomm := commutator_le_frattini hQ
      have : (Q.normalizerMonoidHom ⟨q, Subgroup.le_normalizer hq⟩ x)⁻¹ * x =
          ⁅(⟨q, hq⟩ : Q), x⁻¹⁆ := by
        apply Subtype.ext
        rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.normalizerMonoidHom_apply_apply_coe]
        push_cast
        group
      rw [this]
      exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    · rw [SetLike.mem_coe, MonoidHom.mem_ker]
      have h1 : Q.normalizerMonoidHom ⟨c, Subgroup.centralizer_le_normalizer _ hc⟩ = 1 := by
        rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
        exact hc
      rw [frattiniAction, MonoidHom.comp_apply, h1, map_one]
  obtain ⟨m, hm, hmn⟩ := hker hn
  rw [Subtype.ext hmn] at hm
  exact hm

theorem exists_pow_mem_centralizer {Q : Subgroup X} (hQ : IsPGroup p Q)
    {n : Subgroup.normalizer (Q : Set X)} {k : ℕ} (h : frattiniAction Q n ^ p ^ k = 1) :
    (n : X) ^ p ^ (k + Nat.card (MulAut Q)) ∈ Subgroup.centralizer (Q : Set X) := by
  have h1 : frattiniAut Q (Q.normalizerMonoidHom n ^ p ^ k) = 1 := by
    rw [map_pow]; exact h
  have h2 := exists_pow_eq_one_of_frattiniAut_eq_one hQ h1
  rw [← pow_mul, ← pow_add, ← map_pow] at h2
  have h3 : n ^ p ^ (k + Nat.card (MulAut Q)) ∈ Q.normalizerMonoidHom.ker := h2
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h3
  simpa using h3

theorem eq_sup_of_radical {Q : Subgroup X}
    (hrad : ∀ R : Subgroup X, Q ⊔ Subgroup.centralizer (Q : Set X) ≤ R →
      R ≤ Subgroup.normalizer (Q : Set X) →
      Subgroup.normalizer (Q : Set X) ≤ Subgroup.normalizer (R : Set X) →
      (∃ k : ℕ, ((Q ⊔ Subgroup.centralizer (Q : Set X)).subgroupOf R).index = p ^ k) →
      R = Q ⊔ Subgroup.centralizer (Q : Set X))
    {R : Subgroup X} (h1 : Q ⊔ Subgroup.centralizer (Q : Set X) ≤ R)
    (h2 : R ≤ Subgroup.normalizer (Q : Set X))
    (h3 : Subgroup.normalizer (Q : Set X) ≤ Subgroup.normalizer (R : Set X))
    (hpow : ∀ r ∈ R, ∃ e : ℕ, r ^ p ^ e ∈ Q ⊔ Subgroup.centralizer (Q : Set X)) :
    R = Q ⊔ Subgroup.centralizer (Q : Set X) := by
  refine hrad R h1 h2 h3 ?_
  set K := Q ⊔ Subgroup.centralizer (Q : Set X)
  have hKn : (K.subgroupOf R).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hg : (g : X) ∈ Subgroup.normalizer (K : Set X) :=
      mem_normalizer_sup (h2 g.2) (normalizer_le_normalizer_centralizer Q (h2 g.2))
    simpa using (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hpg : IsPGroup p (R ⧸ K.subgroupOf R) := by
    intro v
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨e, he⟩ := hpow r r.2
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using he
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  exact ⟨k, by rw [Subgroup.index_eq_card, hk]⟩

end CFSG.Walter.Huppert

namespace CFSG.Walter.Huppert

open scoped Pointwise commutatorElement

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

theorem inv_sq_eq_one {V : Type*} [Group V] {σ : MulAut V} (hσ : ∀ v, σ v = v⁻¹) :
    σ ^ 2 = 1 := by
  ext v
  rw [pow_two, MulAut.mul_apply, hσ, hσ, inv_inv, MulAut.one_apply]

theorem eq_of_isAlperinSubgroup (hp2 : p ≠ 2) (P : Sylow p X)
    (hmeta : CFSG.IsMetacyclic (P : Subgroup X)) {Q : Subgroup X}
    (hQ : RankTwoShapes.IsAlperinSubgroup p (P : Subgroup X) Q) : Q = P := by
  classical
  obtain ⟨hQP, hsyl, hcen, hrad⟩ := hQ
  by_contra hne
  have hPp : IsPGroup p (P : Subgroup X) := P.isPGroup'
  have hQp : IsPGroup p Q := hPp.to_le hQP
  obtain ⟨t, htP, htN, htQ⟩ := exists_mem_normalizer_not_mem hPp hQP hne
  set N := Subgroup.normalizer (Q : Set X) with hNdef
  set C := Subgroup.centralizer (Q : Set X) with hCdef
  set ψ := frattiniAction Q with hψdef
  have hF1 : ∀ x : N, (x : X) ∈ Q ⊔ C → ψ x = 1 := fun x hx => frattiniAction_eq_one hQp hx
  have hmk : ∀ (n : N) (x : Q), ψ n (x : Q ⧸ frattini Q) =
      ((Q.normalizerMonoidHom n x : Q) : Q ⧸ frattini Q) := fun n x => frattiniAction_mk Q n x
  have hpowC : ∀ (n : N) (k : ℕ), ψ n ^ p ^ k = 1 →
      (n : X) ^ p ^ (k + Nat.card (MulAut Q)) ∈ C := fun n k h => exists_pow_mem_centralizer hQp h
  clear_value ψ
  set T : Subgroup N := (P : Subgroup X).subgroupOf N with hTdef
  have hTp : IsPGroup p T := hPp.comap_of_injective N.subtype N.subtype_injective
  have hTidx : ¬ p ∣ T.index := by
    have h := hsyl
    rw [Subgroup.inf_subgroupOf_right] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp h
  have hF2 : ∀ x : N, ψ x ∈ T.map ψ → ∃ e : ℕ, (x : X) ^ p ^ e ∈ Q ⊔ C := by
    rintro x ⟨y, hy, hxy⟩
    obtain ⟨e, he⟩ := hTp ⟨y, hy⟩
    have he' : y ^ p ^ e = 1 := congrArg Subtype.val he
    have : ψ x ^ p ^ e = 1 := by rw [← hxy, ← map_pow, he', map_one]
    exact ⟨_, Subgroup.mem_sup_right (hpowC x e this)⟩
  set R : Subgroup X := ((T.map ψ).comap ψ).map N.subtype with hRdef
  have hmemR : ∀ x : N, (x : X) ∈ R ↔ ψ x ∈ T.map ψ := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      rw [← Subtype.ext hyx]
      exact hy
    · intro h
      exact ⟨x, h, rfl⟩
  have hRN : R ≤ N := Subgroup.map_subtype_le _
  clear_value R
  have hQCN : Q ⊔ C ≤ N := sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
  have hQCR : Q ⊔ C ≤ R := by
    intro x hx
    refine (hmemR ⟨x, hQCN hx⟩).mpr ?_
    rw [hF1 ⟨x, hQCN hx⟩ hx]
    exact Subgroup.one_mem _
  have hT₀R : (P : Subgroup X) ⊓ N ≤ R := fun x hx =>
    (hmemR ⟨x, hx.2⟩).mpr (Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hx.1, rfl⟩)
  have hstep : ∃ g t₀ : N, t₀ ∈ T ∧ ψ (g * t₀ * g⁻¹) ∉ T.map ψ := by
    by_contra hcon
    push Not at hcon
    have key : ∀ (g : N) (r : X), r ∈ R → (g : X) * r * (g : X)⁻¹ ∈ R := by
      intro g r hr
      have hrN := hRN hr
      obtain ⟨y, hy, hyr⟩ := (hmemR ⟨r, hrN⟩).mp hr
      have h1 : ψ (g * ⟨r, hrN⟩ * g⁻¹) ∈ T.map ψ := by
        rw [map_mul, map_mul, ← hyr, ← map_mul, ← map_mul]
        exact hcon g y hy
      exact (hmemR (g * ⟨r, hrN⟩ * g⁻¹)).mpr h1
    have hRnorm : N ≤ Subgroup.normalizer (R : Set X) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · exact key ⟨g, hg⟩ r
      · intro hr
        have := key ⟨g, hg⟩⁻¹ _ hr
        simpa [mul_assoc] using this
    have hReq := eq_sup_of_radical hrad hQCR hRN hRnorm fun r hr =>
      hF2 ⟨r, hRN hr⟩ ((hmemR ⟨r, hRN hr⟩).mp hr)
    exact htQ (mem_of_mem_sup_centralizer hQP hcen htP (hReq ▸ hT₀R ⟨htP, htN⟩))
  obtain ⟨g, t₀, ht₀T, hnot⟩ := hstep
  obtain ⟨e₀, he₀⟩ := hTp ⟨t₀, ht₀T⟩
  have ht₀pow : t₀ ^ p ^ e₀ = 1 := congrArg Subtype.val he₀
  have hu₁ : ψ t₀ ^ p ^ e₀ = 1 := by rw [← map_pow, ht₀pow, map_one]
  have hu₂ : ψ (g * t₀ * g⁻¹) ^ p ^ e₀ = 1 := by
    rw [← map_pow, conj_pow, ht₀pow, mul_one, mul_inv_cancel, map_one]
  have hu₂nm : ψ (g * t₀ * g⁻¹) ∉ Subgroup.zpowers (ψ t₀) := fun h =>
    hnot (Subgroup.zpowers_le.mpr (Subgroup.mem_map.mpr ⟨t₀, ht₀T, rfl⟩) h)
  have hu₁1 : ψ t₀ ≠ 1 := by
    intro h1
    apply hnot
    rw [map_mul, map_mul, h1, mul_one, ← map_mul, mul_inv_cancel, map_one]
    exact Subgroup.one_mem _
  have hQmeta : CFSG.IsMetacyclic Q := isMetacyclic_of_le hQP hmeta
  have hVdvd : Nat.card (Q ⧸ frattini Q) ∣ p ^ 2 := card_frattini_quotient_dvd_sq hQp hQmeta
  have hVnot : ¬ Nat.card (Q ⧸ frattini Q) ∣ p := fun h => hu₁1 (eq_one_of_card_dvd hu₁ h)
  have hVcard : Nat.card (Q ⧸ frattini Q) = p ^ 2 := by
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp.out).mp hVdvd
    interval_cases k
    · exact absurd (by rw [hkeq, pow_zero]; exact one_dvd p) hVnot
    · exact absurd (by rw [hkeq, pow_one]) hVnot
    · exact hkeq
  obtain ⟨hVcomm, hVpow⟩ := frattini_quotient_facts hQp
  have hV : Plane p (Q ⧸ frattini Q) := ⟨hVcomm, hVpow, hVcard⟩
  obtain ⟨k, hk⟩ := hV.exists_inv_of_not_mem_zpowers hu₁ hu₂ hu₁1 hu₂nm
  set n₀ : N := (t₀ * (g * t₀ * g⁻¹) ^ k * t₀) ^ 2 with hn₀
  have hψn₀ : ∀ v, ψ n₀ v = v⁻¹ := by
    intro v
    rw [hn₀, map_pow, map_mul, map_mul, map_pow]
    exact hk v
  have hcentral : ∀ σ : MulAut (Q ⧸ frattini Q), ψ n₀ * σ = σ * ψ n₀ := by
    intro σ
    ext v
    simp only [MulAut.mul_apply, hψn₀, map_inv]
  have hn₀R : ∀ r ∈ R, (n₀ : X) * r * (n₀ : X)⁻¹ ∈ R := by
    intro r hr
    have hrN := hRN hr
    have h1 := (hmemR ⟨r, hrN⟩).mp hr
    have h2 : ψ (n₀ * ⟨r, hrN⟩ * n₀⁻¹) = ψ ⟨r, hrN⟩ := by
      rw [map_mul, map_mul, hcentral, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    exact (hmemR (n₀ * ⟨r, hrN⟩ * n₀⁻¹)).mpr (h2 ▸ h1)
  set T₀ : Subgroup X := (P : Subgroup X) ⊓ N with hT₀def
  have hT₀p : IsPGroup p T₀ := hPp.to_le inf_le_left
  set T₂ : Subgroup X := T₀.map (MulAut.conj (n₀ : X)).toMonoidHom with hT₂def
  have hT₂R : T₂ ≤ R := by
    rintro _ ⟨y, hy, rfl⟩
    exact hn₀R y (hT₀R hy)
  have hT₂p : IsPGroup p T₂ := hT₀p.map _
  have hT₂card : Nat.card T₂ = Nat.card T₀ :=
    Subgroup.card_map_of_injective (MulAut.conj (n₀ : X)).injective
  have hidxR : ¬ p ∣ T₀.relIndex R := by
    intro hdvd
    apply hTidx
    have h1 := Subgroup.relIndex_mul_relIndex T₀ R N hT₀R hRN
    have h2 : T₀.relIndex N = T.index := by
      rw [Subgroup.relIndex, hT₀def, Subgroup.inf_subgroupOf_right]
    rw [← h2, ← h1]
    exact Dvd.dvd.mul_right hdvd _
  obtain ⟨r, hrR, hr⟩ := exists_conj_eq hT₀R hT₂R hT₀p hT₂p hidxR hT₂card
  set m : X := r⁻¹ * n₀ with hmdef
  have hmN : m ∈ N := N.mul_mem (N.inv_mem (hRN hrR)) n₀.2
  have hmT₀ : m ∈ Subgroup.normalizer (T₀ : Set X) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro x
    have hx2 : ∀ z : X, z ∈ T₂ ↔ r⁻¹ * z * r ∈ T₀ := by
      intro z
      rw [hr, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have hx1 : ∀ z : X, z ∈ T₂ ↔ (n₀ : X)⁻¹ * z * n₀ ∈ T₀ := by
      intro z
      rw [hT₂def, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    have := (hx1 (r * x * r⁻¹)).symm.trans (hx2 (r * x * r⁻¹))
    rw [hmdef]
    simp only [mul_inv_rev, inv_inv, mul_assoc] at this ⊢
    rw [show r⁻¹ * (r * (x * (r⁻¹ * r))) = x by group] at this
    exact this.symm
  set m' : X := m ^ p ^ Nat.card X with hm'def
  have hm'N : m' ∈ N := N.pow_mem hmN _
  have hm'T₀ : m' ∈ Subgroup.normalizer (T₀ : Set X) := Subgroup.pow_mem _ hmT₀ _
  have hm'cop : Nat.Coprime p (orderOf m') := coprime_orderOf_pow_card m
  have hodd : Odd (p ^ Nat.card X) := (hp.out.odd_of_ne_two hp2).pow
  have hψm' : ∀ v, ψ ⟨m', hm'N⟩ v = v⁻¹ := by
    have hψm : ψ ⟨m, hmN⟩ = (ψ ⟨r, hRN hrR⟩)⁻¹ * ψ n₀ := by
      rw [← map_inv, ← map_mul]
      rfl
    obtain ⟨y, hy, hyr⟩ := (hmemR ⟨r, hRN hrR⟩).mp hrR
    obtain ⟨ey, hey⟩ := hTp ⟨y, hy⟩
    have hy1 : y ^ p ^ Nat.card X = 1 := by
      apply Subtype.ext
      have : (y : X) ^ p ^ ey = 1 := by
        have := congrArg (fun z : T => ((z : N) : X)) hey
        simpa using this
      simpa using pow_card_eq_one_of_isPGroup_elem this
    have hpsi : ψ ⟨m', hm'N⟩ = ψ ⟨m, hmN⟩ ^ p ^ Nat.card X := by
      rw [← map_pow]
      rfl
    have hcomm : Commute (ψ ⟨r, hRN hrR⟩)⁻¹ (ψ n₀) := (hcentral _).symm
    rw [hpsi, hψm, hcomm.mul_pow, inv_pow, ← hyr, ← map_pow, hy1, map_one, inv_one, one_mul]
    obtain ⟨j, hj⟩ := hodd
    intro v
    rw [hj, pow_succ, pow_mul, inv_sq_eq_one hψn₀, one_pow, one_mul, hψn₀]
  set A : Subgroup X := Subgroup.zpowers m' with hAdef
  have hAT : A ≤ Subgroup.normalizer (T₀ : Set X) := Subgroup.zpowers_le.mpr hm'T₀
  let : MulDistribMulAction A T₀ := MulDistribMulAction.compHom T₀ (Subgroup.inclusion hAT)
  have hsmul : ∀ (a : A) (x : T₀), ((a • x : T₀) : X) = (a : X) * x * (a : X)⁻¹ := fun _ _ => rfl
  have : Fact (IsPGroup p T₀) := ⟨hT₀p⟩
  have hT₀meta : CFSG.IsMetacyclic T₀ := isMetacyclic_of_le inf_le_left hmeta
  have hAcop : Nat.Coprime p (Nat.card A) := by rw [Nat.card_zpowers]; exact hm'cop
  have hQT₀ : Q ≤ T₀ := le_inf hQP Subgroup.le_normalizer
  have hT₀nab : ¬ IsMulCommutative T₀ := by
    intro hab
    have htC : t ∉ C := fun htC => htQ (hcen ⟨htC, htP⟩)
    rw [hCdef, Subgroup.mem_centralizer_iff] at htC
    push Not at htC
    obtain ⟨q, hq, hqt⟩ := htC
    apply hqt
    have := hab.is_comm.comm ⟨q, hQT₀ hq⟩ ⟨t, htP, htN⟩
    exact congrArg Subtype.val this
  have hntriv : ¬ CFSG.ActsTrivially A T₀ := by
    intro htriv
    have : Nontrivial (Q ⧸ frattini Q) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hVcard]
      exact one_lt_pow₀ hp.out.one_lt two_ne_zero
    obtain ⟨v, hv⟩ := exists_ne (1 : Q ⧸ frattini Q)
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
      apply hv
      have h1 : ψ ⟨m', hm'N⟩ (x : Q ⧸ frattini Q) = (x : Q ⧸ frattini Q) := by
        rw [hmk]
        congr 1
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        have := htriv ⟨m', Subgroup.mem_zpowers m'⟩ ⟨x, hQT₀ x.2⟩
        have := congrArg Subtype.val this
        rw [hsmul] at this
        exact this
      rw [hψm'] at h1
      have h2 : (x : Q ⧸ frattini Q) ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [← h1]
        exact inv_mul_cancel _
      have h3 := hVpow (x : Q ⧸ frattini Q)
      have hcop2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).mpr hp2.symm
      have := orderOf_dvd_of_pow_eq_one h2
      have := orderOf_dvd_of_pow_eq_one h3
      have h4 : orderOf (x : Q ⧸ frattini Q) = 1 := Nat.eq_one_of_dvd_coprimes hcop2 ‹_› ‹_›
      exact orderOf_eq_one_iff.mp h4
  obtain ⟨-, hcyc, -, -, -⟩ := CFSG.theorem_4_12_c (R := T₀) (A := A) hp2 hAcop hT₀meta hT₀nab
    hntriv
  set D : Subgroup X := (CFSG.commutatorAction A T₀).map T₀.subtype with hDdef
  have hDcyc : IsCyclic D :=
    ((CFSG.commutatorAction A T₀).equivMapOfInjective T₀.subtype T₀.subtype_injective).isCyclic.mp
      hcyc
  have hQD : Q ≤ D := by
    have htop : D.subgroupOf Q ⊔ frattini Q = ⊤ := by
      rw [eq_top_iff]
      intro q _
      set x : Q := q ^ ((p - 1) / 2) with hxdef
      set y : Q := Q.normalizerMonoidHom ⟨m', hm'N⟩ x with hydef
      have hdD : ((x⁻¹ * y : Q) : X) ∈ D := by
        refine ⟨(⟨x, hQT₀ x.2⟩ : T₀)⁻¹ * ((⟨m', Subgroup.mem_zpowers m'⟩ : A) • ⟨x, hQT₀ x.2⟩),
          Subgroup.subset_closure ⟨_, _, Subgroup.mem_top _, rfl⟩, ?_⟩
        rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hsmul, Subgroup.coe_mul,
          Subgroup.coe_inv, hydef, Subgroup.normalizerMonoidHom_apply_apply_coe]
      have h2dvd : 2 ∣ p - 1 := by
        obtain ⟨j, hj⟩ := hp.out.odd_of_ne_two hp2
        exact ⟨j, by omega⟩
      have hxx : (x : Q ⧸ frattini Q) * (x : Q ⧸ frattini Q) =
          (q : Q ⧸ frattini Q) ^ (p - 1) := by
        rw [hxdef, QuotientGroup.mk_pow, ← pow_add, ← two_mul, Nat.mul_div_cancel' h2dvd]
      have hq : ((x⁻¹ * y : Q) : Q ⧸ frattini Q) = (q : Q ⧸ frattini Q) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hydef, ← hmk, hψm', ← mul_inv_rev, hxx,
          inv_eq_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, hVpow]
      have hmem : x⁻¹ * y ∈ D.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hdD
      have : (x⁻¹ * y)⁻¹ * q ∈ frattini Q := QuotientGroup.eq.mp hq
      have := Subgroup.mul_mem_sup hmem this
      rwa [mul_inv_cancel_left] at this
    have hDQ := frattini_nongenerating htop
    intro q hq
    have : (⟨q, hq⟩ : Q) ∈ D.subgroupOf Q := hDQ ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  have hQcyc : IsCyclic Q := Subgroup.isCyclic_of_le hQD
  exact hVnot (card_frattini_quotient_dvd_of_isCyclic hQp)

end CFSG.Walter.Huppert
