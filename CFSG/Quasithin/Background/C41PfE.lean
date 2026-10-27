module

public import CFSG.Quasithin.Background.C41PfKG
public import CFSG.Quasithin.Background.C41PfD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace C41Pf

variable {G : Type} [Group G] [Finite G]

section Cent

@[expose] noncomputable def centModO2 (K : Subgroup G) : Subgroup G :=
  (quotConjHom K).ker.map (Subgroup.normalizer (K : Set G)).subtype

omit [Finite G] in
theorem centModO2_le_normalizer (K : Subgroup G) :
    centModO2 K ≤ Subgroup.normalizer (K : Set G) :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem mem_centModO2_iff {K : Subgroup G} {g : G} :
    g ∈ centModO2 K ↔ ∃ hg : g ∈ Subgroup.normalizer (K : Set G), quotConjHom K ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

omit [Finite G] in
theorem quotConjHom_eq_one_iff {K : Subgroup G} (g : ↥(Subgroup.normalizer (K : Set G))) :
    quotConjHom K g = 1 ↔ ∀ y ∈ K, (g : G) * y * (g : G)⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
  rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
  constructor
  · intro h y hy
    have h1 := congrArg (fun φ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) =>
      φ ((⟨y⁻¹, K.inv_mem hy⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)) h
    simp only [MulAut.one_apply] at h1
    rw [quotConjHom_mk] at h1
    refine ⟨_, QuotientGroup.eq.mp h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    group
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [quotConjHom_mk, MulAut.one_apply]
      apply QuotientGroup.eq.mpr
      obtain ⟨z, hz, hzv⟩ := h (y⁻¹ : ↥K) (y⁻¹ : ↥K).2
      have hzy : (Subgroup.normalizerMonoidHom K g y)⁻¹ * y = z := by
        apply Subtype.ext
        have hzv' : (z : G) = (g : G) * ((y⁻¹ : ↥K) : G) * (g : G)⁻¹ * ((y⁻¹ : ↥K) : G)⁻¹ := hzv
        rw [hzv']
        simp only [Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.normalizerMonoidHom_apply_apply_coe]
        group
      rw [hzy]
      exact hz

omit [Finite G] in
theorem quotConjHom_of_mem {K : Subgroup G} (k : ↥K) :
    quotConjHom K ⟨k, Subgroup.le_normalizer k.2⟩ =
      MulAut.conj ((k : ↥K ⧸ CFSG.pCore 2 ↥K)) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H y =>
    rw [quotConjHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1

omit [Finite G] in
theorem normalizer_le_normalizer_centModO2 (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (centModO2 K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨hxN, hx1⟩ := mem_centModO2_iff.mp hx
    refine mem_centModO2_iff.mpr ⟨(Subgroup.normalizer (K : Set G)).mul_mem
      ((Subgroup.normalizer (K : Set G)).mul_mem hg hxN)
      ((Subgroup.normalizer (K : Set G)).inv_mem hg), ?_⟩
    have e : (⟨g * x * g⁻¹, _⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨g, hg⟩ * ⟨x, hxN⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hx1, mul_one, mul_inv_cancel]
  · intro hx
    obtain ⟨hxN, hx1⟩ := mem_centModO2_iff.mp hx
    have hxN' : x ∈ Subgroup.normalizer (K : Set G) := by
      have := (Subgroup.normalizer (K : Set G)).mul_mem
        ((Subgroup.normalizer (K : Set G)).mul_mem
          ((Subgroup.normalizer (K : Set G)).inv_mem hg) hxN) hg
      simpa [mul_assoc] using this
    refine mem_centModO2_iff.mpr ⟨hxN', ?_⟩
    have e : (⟨x, hxN'⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨g, hg⟩⁻¹ * ⟨g * x * g⁻¹, hxN⟩ * ⟨g, hg⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, map_mul, map_mul, map_inv, hx1, mul_one, inv_mul_cancel]

omit [Finite G] in
theorem pCoreOf_le_centModO2 (K : Subgroup G) : pCoreOf 2 K ≤ centModO2 K := by
  intro q hq
  have hqN : q ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer (pCoreOf_le 2 K hq)
  refine mem_centModO2_iff.mpr ⟨hqN, (quotConjHom_eq_one_iff _).mpr fun y hy => ?_⟩
  have h1 : y * q⁻¹ * y⁻¹ ∈ pCoreOf 2 K :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hy) q⁻¹).mp
      ((pCoreOf 2 K).inv_mem hq)
  have e : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
  show q * y * q⁻¹ * y⁻¹ ∈ pCoreOf 2 K
  rw [e]
  exact (pCoreOf 2 K).mul_mem hq h1

omit [Finite G] in
theorem commutator_le_of_le_centModO2 {K X : Subgroup G} (hX : X ≤ centModO2 K) :
    ⁅X, K⁆ ≤ pCoreOf 2 K := by
  rw [Subgroup.commutator_le]
  intro g hg y hy
  obtain ⟨hgN, hg1⟩ := mem_centModO2_iff.mp (hX hg)
  rw [commutatorElement_def]
  exact (quotConjHom_eq_one_iff ⟨g, hgN⟩).mp hg1 y hy

omit [Finite G] in
theorem le_centModO2_of_commutator_le {K X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hX : ⁅X, K⁆ ≤ pCoreOf 2 K) :
    X ≤ centModO2 K := by
  intro g hg
  refine mem_centModO2_iff.mpr ⟨hXN hg, (quotConjHom_eq_one_iff _).mpr fun y hy => ?_⟩
  have := Subgroup.commutator_mem_commutator hg hy
  rw [commutatorElement_def] at this
  exact hX this

end Cent

section Frattini

theorem le_pCoreOf_of_isSylowTwoOf_cent {K R S : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf S ((K ⊔ R) ⊓ centModO2 K)) :
    (∀ x ∈ (K ⊔ R) ⊓ centModO2 K, (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ S) ∧
      S ≤ pCoreOf 2 (K ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := (K ⊔ R) ⊓ centModO2 K with hD
  set Q := pCoreOf 2 K with hQ
  have hBN : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRN
  have hDN : D ≤ Subgroup.normalizer (K : Set G) := inf_le_right.trans (centModO2_le_normalizer K)
  have hBD : K ⊔ R ≤ Subgroup.normalizer (D : Set G) :=
    (le_inf Subgroup.le_normalizer (hBN.trans (normalizer_le_normalizer_centModO2 K))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hQD : Q ≤ D := le_inf ((pCoreOf_le 2 K).trans le_sup_left) (pCoreOf_le_centModO2 K)
  have hQS : Q ≤ S := by
    refine A4.le_of_normal_of_isSylowTwoOf hS hQD ?_ (pCoreOf_isPGroup 2 K)
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (hDN.trans (normalizer_le_normalizer_pCoreOf 2 K))
  have hKS : K ≤ Subgroup.normalizer (S : Set G) := by
    intro z hz
    refine A4.mem_normalizer_of_conj_mem fun s hs => ?_
    obtain ⟨hsN, hs1⟩ := mem_centModO2_iff.mp (hS.1 hs).2
    have h1 : s * z⁻¹ * s⁻¹ * (z⁻¹)⁻¹ ∈ Q :=
      (quotConjHom_eq_one_iff ⟨s, hsN⟩).mp hs1 z⁻¹ (K.inv_mem hz)
    have h2 : z * (s * z⁻¹ * s⁻¹ * (z⁻¹)⁻¹) * z⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hz) _).mp h1
    have e : z * s * z⁻¹ = (z * (s * z⁻¹ * s⁻¹ * (z⁻¹)⁻¹) * z⁻¹) * s := by group
    rw [e]
    exact S.mul_mem (hQS h2) hs
  have hDle : D ≤ S ⊔ (D ⊓ K) := by
    set T := S ⊔ (D ⊓ K) with hT
    have hST : S ≤ T := le_sup_left
    have hTD : T ≤ D := sup_le hS.1 inf_le_left
    have hodd : ¬ 2 ∣ S.relIndex D := hS.2.2
    have h1 : T.relIndex D ∣ S.relIndex D :=
      Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex S T D hST hTD)
    have h2 : T.relIndex D ∣ (D ⊓ K).relIndex D :=
      Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex (D ⊓ K) T D le_sup_right hTD)
    have h3 : (D ⊓ K).relIndex D = K.relIndex D := by
      rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.inf_subgroupOf_left]
    have h4 : K.relIndex D = K.relIndex (D ⊔ K) :=
      (A4.relIndex_sup_eq_of_le_normalizer' hDN).symm
    have h5 : K.relIndex (D ⊔ K) ∣ K.relIndex (K ⊔ R) :=
      Dvd.intro _ (Subgroup.relIndex_mul_relIndex K (D ⊔ K) (K ⊔ R) le_sup_right
        (sup_le (inf_le_left) le_sup_left))
    have h6 : K.relIndex (K ⊔ R) = K.relIndex R := by
      rw [sup_comm]
      exact A4.relIndex_sup_eq_of_le_normalizer' hRN
    obtain ⟨n, hn⟩ := hR2.index (K.subgroupOf R)
    have h7 : T.relIndex D ∣ 2 ^ n := by
      have : K.relIndex R = 2 ^ n := hn
      rw [← this, ← h6]
      exact h2.trans (h3 ▸ h4 ▸ h5)
    have h8 : T.relIndex D = 1 := by
      have hcop : Nat.Coprime (T.relIndex D) (S.relIndex D) := by
        apply Nat.Coprime.coprime_dvd_left h7
        apply Nat.Coprime.pow_left
        exact (Nat.prime_two.coprime_iff_not_dvd).mpr hodd
      exact Nat.Coprime.eq_one_of_dvd hcop h1
    exact Subgroup.relIndex_eq_one.mp h8
  have hDS : D ≤ Subgroup.normalizer (S : Set G) :=
    hDle.trans (sup_le Subgroup.le_normalizer (inf_le_right.trans hKS))
  have hmem : ∀ x ∈ D, (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ S := fun x hx h2 =>
    C24Pf.mem_of_mem_normalizer_of_isSylowTwoOf hS hx (hDS hx) h2
  refine ⟨hmem, ?_⟩
  refine le_pCoreOf_of_le_normalizer 2 (hS.1.trans inf_le_left) ?_ hS.2.1
  intro b hb
  refine A4.mem_normalizer_of_conj_mem fun s hs => ?_
  have hsD : b * s * b⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hBD hb) s).mp (hS.1 hs)
  refine hmem _ hsD ?_
  obtain ⟨n, hn⟩ := hS.2.1 ⟨s, hs⟩
  refine ⟨n, ?_⟩
  have hs' : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  rw [conj_pow, hs', mul_one, mul_inv_cancel]

theorem isSylowTwoOf_sup_cent {K R : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hR2 : IsPGroup 2 R)
    (hO2 : pCoreOf 2 (K ⊔ R) ≤ R) : IsSylowTwoOf R (R ⊔ ((K ⊔ R) ⊓ centModO2 K)) := by
  set D := (K ⊔ R) ⊓ centModO2 K with hD
  obtain ⟨S, hS, -⟩ := A4.exists_isSylowTwoOf_ge (P := ⊥) (H := D) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  obtain ⟨hmem, hSO⟩ := le_pCoreOf_of_isSylowTwoOf_cent hRN hR2 hS
  have hBN : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRN
  have hRD : R ≤ Subgroup.normalizer (D : Set G) :=
    (le_inf (le_sup_right.trans Subgroup.le_normalizer)
      ((le_sup_right.trans hBN).trans (normalizer_le_normalizer_centModO2 K))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_left, hR2, fun P hP hP2 hRP => ?_⟩
  intro x hx
  have hxRD : x ∈ ((R ⊔ D : Subgroup G) : Set G) := hP hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right R D hRD] at hxRD
  obtain ⟨r, hr, d, hd, rfl⟩ := hxRD
  have hdP : d ∈ P := by
    have := P.mul_mem (P.inv_mem (hRP hr)) hx
    simpa using this
  obtain ⟨n, hn⟩ := hP2 ⟨d, hdP⟩
  have hd2 : d ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact R.mul_mem hr (hO2 (hSO (hmem d hd ⟨n, hd2⟩)))

theorem exists_mem_inf_of_quotConjHom_eq {K R M : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hR2 : IsPGroup 2 R)
    (hO2 : pCoreOf 2 (K ⊔ R) ≤ R) (hRM : R ≤ M)
    (hNM : (K ⊔ R) ⊓ Subgroup.normalizer (R : Set G) ≤ M) {l k : G}
    (hlK : l ∈ Subgroup.normalizer (K : Set G)) (hlR : l ∈ Subgroup.normalizer (R : Set G))
    (hk : k ∈ K) (hψ : quotConjHom K ⟨l, hlK⟩ = quotConjHom K ⟨k, Subgroup.le_normalizer hk⟩) :
    ∃ n ∈ M ⊓ (K ⊔ R), ∃ hn : n ∈ Subgroup.normalizer (K : Set G),
      quotConjHom K ⟨n, hn⟩ = quotConjHom K ⟨l, hlK⟩ := by
  set N := Subgroup.normalizer (K : Set G) with hN
  set D := (K ⊔ R) ⊓ centModO2 K with hD
  have hBN : K ⊔ R ≤ N := sup_le Subgroup.le_normalizer hRN
  have hBD : K ⊔ R ≤ Subgroup.normalizer (D : Set G) :=
    (le_inf Subgroup.le_normalizer (hBN.trans (normalizer_le_normalizer_centModO2 K))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hRD : R ≤ Subgroup.normalizer (D : Set G) := le_sup_right.trans hBD
  have hRsyl := isSylowTwoOf_sup_cent hRN hR2 hO2
  have hconj : ∀ (l' k' : G) (hl'K : l' ∈ N) (_ : l' ∈ Subgroup.normalizer (R : Set G))
      (hk' : k' ∈ K), quotConjHom K ⟨l', hl'K⟩ = quotConjHom K ⟨k', Subgroup.le_normalizer hk'⟩ →
      ∀ r ∈ R, k' * r * k'⁻¹ ∈ R ⊔ D := by
    intro l' k' hl'K hl'R hk' hψ' r hr
    have hr' : l' * r * l'⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hl'R r).mp hr
    have hxB : (l' * r * l'⁻¹)⁻¹ * (k' * r * k'⁻¹) ∈ K ⊔ R :=
      (K ⊔ R).mul_mem ((K ⊔ R).inv_mem (Subgroup.mem_sup_right hr'))
        ((K ⊔ R).mul_mem ((K ⊔ R).mul_mem (Subgroup.mem_sup_left hk')
          (Subgroup.mem_sup_right hr)) ((K ⊔ R).inv_mem (Subgroup.mem_sup_left hk')))
    have hxD : (l' * r * l'⁻¹)⁻¹ * (k' * r * k'⁻¹) ∈ D := by
      refine ⟨hxB, mem_centModO2_iff.mpr ⟨hBN hxB, ?_⟩⟩
      have e : (⟨(l' * r * l'⁻¹)⁻¹ * (k' * r * k'⁻¹), hBN hxB⟩ : ↥N) =
          ((⟨l', hl'K⟩ : ↥N) * ⟨r, hRN hr⟩ * (⟨l', hl'K⟩ : ↥N)⁻¹)⁻¹ *
            ((⟨k', Subgroup.le_normalizer hk'⟩ : ↥N) * ⟨r, hRN hr⟩ *
              (⟨k', Subgroup.le_normalizer hk'⟩ : ↥N)⁻¹) := rfl
      rw [e]
      simp only [map_mul, map_inv, hψ']
      group
    have e : k' * r * k'⁻¹ = (l' * r * l'⁻¹) * ((l' * r * l'⁻¹)⁻¹ * (k' * r * k'⁻¹)) := by group
    rw [e]
    exact (R ⊔ D).mul_mem (Subgroup.mem_sup_left hr') (Subgroup.mem_sup_right hxD)
  have hk1 := hconj l k hlK hlR hk hψ
  have hkinv : quotConjHom K ⟨l⁻¹, N.inv_mem hlK⟩ =
      quotConjHom K ⟨k⁻¹, Subgroup.le_normalizer (K.inv_mem hk)⟩ := by
    have e1 : (⟨l⁻¹, N.inv_mem hlK⟩ : ↥N) = (⟨l, hlK⟩ : ↥N)⁻¹ := rfl
    have e2 : (⟨k⁻¹, Subgroup.le_normalizer (K.inv_mem hk)⟩ : ↥N) =
        (⟨k, Subgroup.le_normalizer hk⟩ : ↥N)⁻¹ := rfl
    rw [e1, e2, map_inv, map_inv, hψ]
  have hk2 := hconj l⁻¹ k⁻¹ (N.inv_mem hlK) (Subgroup.normalizer (R : Set G) |>.inv_mem hlR)
    (K.inv_mem hk) hkinv
  have hkD : k ∈ Subgroup.normalizer (D : Set G) := hBD (Subgroup.mem_sup_left hk)
  have hkmap : ∀ g : G, g ∈ Subgroup.normalizer (D : Set G) → (∀ r ∈ R, g * r * g⁻¹ ∈ R ⊔ D) →
      ∀ x ∈ R ⊔ D, g * x * g⁻¹ ∈ R ⊔ D := by
    intro g hgD hgR x hx
    have hle : R ⊔ D ≤ (R ⊔ D).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun r hr => hgR r hr) fun d hd => ?_
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hgD d).mp hd)
    exact hle hx
  have hkRD : k ∈ Subgroup.normalizer ((R ⊔ D : Subgroup G) : Set G) :=
    A4.mem_normalizer_of_conj_mem (hkmap k hkD hk1)
  have hkRsyl : IsSylowTwoOf (conjByElt k R) (R ⊔ D) := by
    rw [A4.isSylowTwoOf_iff_maximal]
    refine ⟨?_, hR2.map _, fun P hP hP2 hRP => ?_⟩
    · rintro _ ⟨r, hr, rfl⟩
      exact hk1 r hr
    · have hPc : conjByElt k⁻¹ P ≤ R ⊔ D := by
        rintro _ ⟨p, hp, rfl⟩
        have := hkmap k⁻¹ (Subgroup.normalizer (D : Set G) |>.inv_mem hkD) (by simpa using hk2)
          p (hP hp)
        simpa using this
      have hRc : R ≤ conjByElt k⁻¹ P := by
        intro r hr
        refine ⟨k * r * k⁻¹, hRP ⟨r, hr, rfl⟩, ?_⟩
        simp [mul_assoc]
      have hmax := ((A4.isSylowTwoOf_iff_maximal.mp hRsyl).2.2 _ hPc (hP2.map _) hRc)
      intro p hp
      have : k⁻¹ * p * k⁻¹⁻¹ ∈ R := hmax ⟨p, hp, rfl⟩
      refine ⟨k⁻¹ * p * k⁻¹⁻¹, this, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  obtain ⟨h, hh, hhc⟩ := A4.exists_conj_of_isSylowTwoOf hRsyl hkRsyl
  have hn0R : h⁻¹ * k ∈ Subgroup.normalizer (R : Set G) := by
    refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
    have hky : k * y * k⁻¹ ∈ conjByElt k R := ⟨y, hy, rfl⟩
    have := (hhc _).mp hky
    have e : h⁻¹ * k * y * (h⁻¹ * k)⁻¹ = h⁻¹ * (k * y * k⁻¹) * h := by group
    rw [e]
    exact this
  have hhB : h ∈ K ⊔ R := (sup_le le_sup_right inf_le_left : R ⊔ D ≤ K ⊔ R) hh
  have hn0B : h⁻¹ * k ∈ K ⊔ R := (K ⊔ R).mul_mem ((K ⊔ R).inv_mem hhB) (Subgroup.mem_sup_left hk)
  have hn0M : h⁻¹ * k ∈ M := hNM ⟨hn0B, hn0R⟩
  have hhRD : h ∈ ((R ⊔ D : Subgroup G) : Set G) := hh
  rw [Subgroup.coe_mul_of_left_le_normalizer_right R D hRD] at hhRD
  obtain ⟨r₀, hr₀, d₀, hd₀, hrd⟩ := hhRD
  have hnB : r₀ * (h⁻¹ * k) ∈ K ⊔ R := (K ⊔ R).mul_mem (Subgroup.mem_sup_right hr₀) hn0B
  refine ⟨r₀ * (h⁻¹ * k), ⟨M.mul_mem (hRM hr₀) hn0M, hnB⟩, hBN hnB, ?_⟩
  obtain ⟨hd₀N, hd₀1⟩ := mem_centModO2_iff.mp hd₀.2
  have e : (⟨r₀ * (h⁻¹ * k), hBN hnB⟩ : ↥N) =
      (⟨r₀, hRN hr₀⟩ : ↥N) * (⟨d₀, hd₀N⟩ : ↥N)⁻¹ * (⟨r₀, hRN hr₀⟩ : ↥N)⁻¹ *
        ⟨k, Subgroup.le_normalizer hk⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hrd]
    group
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hd₀1, ← hψ]
  group

end Frattini

section Projection

theorem le_of_perfect_of_le_sup {K R P : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hR2 : IsPGroup 2 R) (hP : ⁅P, P⁆ = P)
    (hPB : P ≤ K ⊔ R) : P ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := K ⊔ R with hB
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRN
  have hKn : (K.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hBN
  set φ := QuotientGroup.mk' (K.subgroupOf B) with hφ
  obtain ⟨n, hn⟩ := hR2.index (K.subgroupOf R)
  have hcard : Nat.card (↥B ⧸ K.subgroupOf B) = 2 ^ n := by
    rw [← Subgroup.index_eq_card]
    change K.relIndex B = 2 ^ n
    rw [hB, sup_comm, A4.relIndex_sup_eq_of_le_normalizer' hRN]
    exact hn
  have hqs : Group.IsSolvable (↥B ⧸ K.subgroupOf B) := by
    have := (IsPGroup.of_card hcard).isNilpotent
    infer_instance
  set P' := (P.subgroupOf B).map φ with hP'
  have hP'p : ⁅P', P'⁆ = P' := by
    rw [hP', ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPB, hP]
  have hbot := eq_bot_of_perfect_of_isSolvable hP'p inferInstance
  intro x hx
  have hmem : φ ⟨x, hPB hx⟩ ∈ P' := ⟨⟨x, hPB hx⟩, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact hmem

omit [Finite G] in
theorem commutator_le_of_le {N A B : Subgroup G} (hA : A ≤ N) (hB : B ≤ N) : ⁅A, B⁆ ≤ N :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem (hA ha) (hB hb)) (N.inv_mem (hA ha))) (N.inv_mem (hB hb))

omit [Finite G] in
theorem commutator_subgroupOf {N Y₁ Y₂ : Subgroup G} (h₁ : Y₁ ≤ N) (h₂ : Y₂ ≤ N) :
    ⁅Y₁.subgroupOf N, Y₂.subgroupOf N⁆ = ⁅Y₁, Y₂⁆.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁,
    Subgroup.map_subgroupOf_eq_of_le h₂,
    Subgroup.map_subgroupOf_eq_of_le (commutator_le_of_le h₁ h₂)]

theorem le_or_commutator_le_of_cComp {K R M L' : Subgroup G}
    (hOut : OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hRN : R ≤ Subgroup.normalizer (K : Set G)) (hR2 : IsPGroup 2 R)
    (hO2 : pCoreOf 2 (K ⊔ R) ≤ R) (hRM : R ≤ M)
    (hNM : (K ⊔ R) ⊓ Subgroup.normalizer (R : Set G) ≤ M) (hL' : L' ∈ cComp M)
    (hL'K : L' ≤ Subgroup.normalizer (K : Set G)) (hL'R : L' ≤ Subgroup.normalizer (R : Set G)) :
    L' ≤ K ∨ ⁅L', K⁆ ≤ pCoreOf 2 K := by
  set N := Subgroup.normalizer (K : Set G) with hN
  set X := M ⊓ (K ⊔ R) with hX
  have hL'M : L' ≤ M := le_of_mem_cComp hL'
  have hL'p : ⁅L', L'⁆ = L' := perfect_of_mem_cComp hL'
  have hXM : X ≤ M := inf_le_left
  have hBN : K ⊔ R ≤ N := sup_le Subgroup.le_normalizer hRN
  have hXN : X ≤ N := inf_le_right.trans hBN
  have hL'X : L' ≤ Subgroup.normalizer (X : Set G) := by
    have h1 : L' ≤ Subgroup.normalizer ((K ⊔ R : Subgroup G) : Set G) :=
      (le_inf hL'K hL'R).trans (Subgroup.inf_normalizer_le_normalizer_sup K R)
    exact (le_inf (hL'M.trans Subgroup.le_normalizer) h1).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have htop : ⁅(⊤ : Subgroup ↥L'), (⊤ : Subgroup ↥L')⁆ = (⊤ : Subgroup ↥L') := by
    apply Subgroup.map_injective L'.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hL'p]
  have hDp : Group.IsPerfect ↥L' := Group.isPerfect_def.mpr htop
  have hinner : ∀ (l : G) (hl : l ∈ L'), ∃ (k : G) (hk : k ∈ K),
      quotConjHom K ⟨l, hL'K hl⟩ = quotConjHom K ⟨k, Subgroup.le_normalizer hk⟩ := by
    intro l hl
    obtain ⟨x, hx⟩ := A38.exists_inner_of_outSolvable hOut hDp
      ((quotConjHom K).comp (Subgroup.inclusion hL'K)) ⟨l, hl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨k, k.2, ?_⟩
    rw [quotConjHom_of_mem k]
    exact hx
  have hproj : ∀ (l : G) (hl : l ∈ L'), ∃ n ∈ X, ∃ hn : n ∈ N,
      quotConjHom K ⟨n, hn⟩ = quotConjHom K ⟨l, hL'K hl⟩ := by
    intro l hl
    obtain ⟨k, hk, hψ⟩ := hinner l hl
    exact exists_mem_inf_of_quotConjHom_eq hRN hR2 hO2 hRM hNM (hL'K hl) (hL'R hl) hk hψ
  rcases cComp_commutator_dichotomy_of_le hL' hXM with ⟨-, hsol⟩ | heq
  · right
    set A := (L'.subgroupOf N).map (quotConjHom K) with hA
    set B := (X.subgroupOf N).map (quotConjHom K) with hB
    have hAB : A ≤ B := by
      rintro _ ⟨⟨l, hlN⟩, hl, rfl⟩
      obtain ⟨n, hnX, hnN, hn⟩ := hproj l hl
      exact ⟨⟨n, hnN⟩, hnX, hn⟩
    have hAp : ⁅A, A⁆ = A := by
      rw [hA, ← Subgroup.map_commutator, commutator_subgroupOf hL'K hL'K, hL'p]
    have hcN : ⁅L', X⁆ ≤ N := commutator_le_of_le hL'K hXN
    have hABc : ⁅A, B⁆ = (⁅L', X⁆.subgroupOf N).map (quotConjHom K) := by
      rw [hA, hB, ← Subgroup.map_commutator, commutator_subgroupOf hL'K hXN]
    have hsol' : Group.IsSolvable ↥((⁅L', X⁆.subgroupOf N).map (quotConjHom K)) := by
      have : Group.IsSolvable ↥(⁅L', X⁆.subgroupOf N) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe hcN).toMonoidHom) (MulEquiv.injective _)
      exact Group.isSolvable_of_surjective ((quotConjHom K).subgroupMap_surjective _)
    have hAle : A ≤ (⁅L', X⁆.subgroupOf N).map (quotConjHom K) := by
      rw [← hABc]
      calc A = ⁅A, A⁆ := hAp.symm
        _ ≤ ⁅A, B⁆ := Subgroup.commutator_mono le_rfl hAB
    have hAsol : Group.IsSolvable ↥A :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAle)
        (Subgroup.inclusion_injective hAle)
    have hA1 := eq_bot_of_perfect_of_isSolvable hAp hAsol
    refine Subgroup.commutator_le.mpr fun l hl y hy => ?_
    have hl1 : quotConjHom K ⟨l, hL'K hl⟩ = 1 := by
      have : quotConjHom K ⟨l, hL'K hl⟩ ∈ A := ⟨⟨l, hL'K hl⟩, hl, rfl⟩
      rw [hA1] at this
      exact Subgroup.mem_bot.mp this
    rw [commutatorElement_def]
    exact (quotConjHom_eq_one_iff _).mp hl1 y hy
  · left
    have h1 : L' ≤ X :=
      calc L' ≤ conjClosure L' X := le_conjClosure L' X
        _ = ⁅L', X⁆ := heq.symm
        _ ≤ X := Subgroup.le_normalizer_iff_commutator_le_right.mp hL'X
    exact le_of_perfect_of_le_sup hRN hR2 hL'p (h1.trans inf_le_right)

variable {H R M L V K : Subgroup G}

theorem pCoreOf_sup_le_of_hyp (h : HypC28 H R M L V) (hKH : K ≤ H)
    (hNK : conjClosure L M ≤ Subgroup.normalizer (K : Set G)) : pCoreOf 2 (K ⊔ R) ≤ R := by
  have hRH : R ≤ H := h.le_M.trans h.le_H
  have hYN : conjClosure L M ≤ Subgroup.normalizer ((K ⊔ R : Subgroup G) : Set G) :=
    (le_inf hNK (c2_9_two h).1).trans (Subgroup.inf_normalizer_le_normalizer_sup K R)
  exact c2_1_pCore_le (isTwoRadicalIn_of_le h le_sup_right (sup_le hKH hRH) hYN)

theorem sup_inf_normalizer_le_of_hyp (h : HypC28 H R M L V) (hKH : K ≤ H) :
    (K ⊔ R) ⊓ Subgroup.normalizer (R : Set G) ≤ M :=
  (inf_le_inf_right _ (sup_le hKH (h.le_M.trans h.le_H))).trans (C2Nine.inf_normalizer_le_M h)

theorem conjClosure_le_of_le_normalizer (hOut : OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (h : HypC28 H R M L V) (hKH : K ≤ H) (hRN : R ≤ Subgroup.normalizer (K : Set G))
    (hNK : conjClosure L M ≤ Subgroup.normalizer (K : Set G))
    (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (hnc : ¬ ⁅conjClosure L M, K⁆ ≤ pCoreOf 2 K) : conjClosure L M ≤ K := by
  have hLK : L ≤ Subgroup.normalizer (K : Set G) := (le_conjClosure L M).trans hNK
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := (le_conjClosure L M).trans (c2_9_two h).1
  rcases le_or_commutator_le_of_cComp hOut hRN h.pgroup (pCoreOf_sup_le_of_hyp h hKH hNK)
      h.le_M (sup_inf_normalizer_le_of_hyp h hKH) h.comp hLK hLR with hle | hc
  · exact conjClosure_le fun m hm l hl =>
      (Subgroup.mem_normalizer_iff.mp (hMK hm) l).mp (hle hl)
  · refine absurd (commutator_le_of_le_centModO2 ?_) hnc
    have hLc : L ≤ centModO2 K := le_centModO2_of_commutator_le hLK hc
    exact conjClosure_le fun m hm l hl =>
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centModO2 K (hMK hm)) l).mp
        (hLc hl)

end Projection

end C41Pf

section KZero

variable (G : Type) [Group G] [Finite G]

@[expose] def C41KZero : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → K ∈ cComp H → CharTwo K →
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → ¬ K ≤ M →
    R ≤ Subgroup.normalizer (K : Set G) →
    (∃ P : Subgroup G, P ≠ ⊥ ∧ ⁅P, P⁆ = P ∧ P ≤ M ⊓ K ∧
      P ≤ Subgroup.normalizer (R : Set G)) →
    H ≤ Subgroup.normalizer (K : Set G)

end KZero

namespace C41Pf

variable {G : Type} [Group G] [Finite G]

theorem c41ProjStep_of (hA3 : A3Orbits G)
    (hSch : ∀ K : Subgroup G, IsSQTKIn K → CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) →
      OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K))
    (hK0 : C41KZero G) : C41ProjStep G := by
  intro H R M L V K h hK hKc hKq hKM hRN hnc
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hNK := conjClosure_le_normalizer hA3 h hK
  have hOut := hSch K (h.sqtk.mono hKH) hKq
  have hO2 := pCoreOf_sup_le_of_hyp h hKH hNK
  have hNM := sup_inf_normalizer_le_of_hyp h hKH
  have hcomp : ∀ m ∈ M, conjByElt m L ∈ cComp M := fun m hm =>
    C2Nine.conjByElt_mem_cComp h.comp (Subgroup.le_normalizer hm)
  have hex : ∃ m ∈ M, conjByElt m L ≤ K := by
    by_contra hne
    push Not at hne
    refine hnc (commutator_le_of_le_centModO2 (conjClosure_le fun m hm l hl => ?_))
    have hLmM₀ : conjByElt m L ≤ conjClosure L M := conjByElt_le_conjClosure hm
    have hc := (le_or_commutator_le_of_cComp hOut hRN h.pgroup hO2 h.le_M hNM (hcomp m hm)
      (hLmM₀.trans hNK) (hLmM₀.trans (c2_9_two h).1)).resolve_left (hne m hm)
    have hmem : m * l * m⁻¹ ∈ conjByElt m L := by
      rw [mem_conjByElt]
      simpa [mul_assoc] using hl
    exact le_centModO2_of_commutator_le (hLmM₀.trans hNK) hc hmem
  obtain ⟨m, hm, hmK⟩ := hex
  have hHN := hK0 H R M L V K h hK hKc hKq hKM hRN ⟨conjByElt m L,
    ne_bot_of_mem_cComp (hcomp m hm), perfect_of_mem_cComp (hcomp m hm),
    le_inf (le_of_mem_cComp (hcomp m hm)) hmK,
    (conjByElt_le_conjClosure hm).trans (c2_9_two h).1⟩
  exact conjClosure_le_of_le_normalizer hOut h hKH hRN hNK (h.le_H.trans hHN) hnc

end C41Pf

end CFSG.Quasithin
