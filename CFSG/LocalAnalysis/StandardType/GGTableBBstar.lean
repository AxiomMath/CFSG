module

public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section General

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_zpowers_of_elemAbelian {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    {x : G} {L : Subgroup G} (hE : IsElemAbelian p E) (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S) :
    E ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  have := Fact.mk hp
  have hxC := mem_centralizer_of_le_centralizer hLx
  have hE' : IsElemAbelian p (E ⊓ Subgroup.centralizer (L : Set G)) :=
    isElemAbelian_mono hE inf_le_left
  have hcE := hcyc _ inf_le_right (isPGroup_of_isElemAbelian hE')
  have hle : Subgroup.zpowers x ≤ E ⊓ Subgroup.centralizer (L : Set G) :=
    (Subgroup.zpowers_le).mpr ⟨hxE, hxC⟩
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, orderOf_eq_prime (hE.2 x hxE) hx1]
  exact card_le_of_isCyclic hp.pos hcE hE'.2

theorem ker_ggBeta_of {p : ℕ} (hp : p.Prime) {E : Subgroup G} {x : G} {L : Subgroup G}
    (hE : IsElemAbelian p E) (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) :
    (ggBeta L θ hEN).ker = (Subgroup.zpowers x).subgroupOf E := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
    ← inf_centralizer_eq_zpowers_of_elemAbelian hp hE hxE hx1 hLx hcyc]
  constructor
  · intro h
    exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one L θ hL h⟩
  · rintro ⟨-, hc⟩
    exact ggLAut_eq_one_of_mem_centralizer L θ hc

theorem card_range_ggBeta_mul_of {p : ℕ} (hp : p.Prime) {E : Subgroup G} {x : G}
    {L : Subgroup G} (hE : IsElemAbelian p E) (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hL : commutator L = ⊤) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggBeta L θ hEN).range * p = Nat.card E := by
  have := Fact.mk hp
  have h1 := card_range_mul_card_ker (ggBeta L θ hEN)
  rw [ker_ggBeta_of hp hE hxE hx1 hLx hcyc hL θ hEN] at h1
  have h2 : Nat.card ((Subgroup.zpowers x).subgroupOf E) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxE)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hE.2 x hxE) hx1]
  rwa [h2] at h1

theorem isElemAbelian_range {H : Type*} [Group H] {M : Type*} [Group M] {p : ℕ}
    (hH : ∀ a b : H, a * b = b * a) (hp : ∀ a : H, a ^ p = 1) (f : H →* M) :
    IsElemAbelian p f.range := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, hH]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hp, map_one]

end General

section TwoLift

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_two_zpowers {H : Type*} [Group H] {h : H} {k : ℕ} (hk : h ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers h) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem exists_twoSubgroup_of_normalizes {L : Subgroup G} {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) {E₂ : Subgroup G}
    (hEN : E₂ ≤ Subgroup.normalizer (L : Set G)) {U : Subgroup R} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hEU : ∀ (e : G) (he : e ∈ E₂), ∀ u ∈ U, ggLAut L θ ⟨e, hEN he⟩ u ∈ U) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ E₂ ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite R := Finite.of_equiv _ θ.toEquiv
  set ψ := ggQuotHom θ with hψ
  set H : Subgroup L := U.comap ψ with hH
  let f : H →* U := (ψ.comp H.subtype).codRestrict U (fun h => h.2)
  have hf : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ r
    exact ⟨⟨l, hr⟩, rfl⟩
  have hker : f.ker ≤ Subgroup.center H := by
    intro h hh
    have h1 : ψ h = 1 := congrArg Subtype.val hh
    have h2 : (h : L) ∈ Subgroup.center L := by
      rw [← ker_ggQuotHom θ]
      exact h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro k
    exact Subtype.ext (h2 k)
  have : Group.IsNilpotent U := hU2.isNilpotent
  have : Group.IsNilpotent H := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 H))
  have hPn : (P : Subgroup H).Normal := inferInstance
  have htop : (⊤ : Subgroup U) = (P : Subgroup H).map f := by
    have h := (P.mapSurjective hf).is_maximal' (Q := ⊤)
      (hU2.of_equiv Subgroup.topEquiv.symm) le_top
    rwa [Sylow.coe_mapSurjective] at h
  have hmemP : ∀ h : H, ∀ k : ℕ, h ^ 2 ^ k = 1 → h ∈ (P : Subgroup H) := by
    intro h k hk
    obtain ⟨Q, hQ⟩ := (isPGroup_two_zpowers hk).exists_le_sylow
    have := Sylow.unique_of_normal P hPn
    have hQP : Q = P := Subsingleton.elim Q P
    rw [← hQP]
    exact hQ (Subgroup.mem_zpowers h)
  refine ⟨((P : Subgroup H).map H.subtype).map L.subtype, ?_, (P.isPGroup'.map _).map _, ?_⟩
  · intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at hbot
    rw [hbot, Subgroup.map_bot] at htop
    apply hU
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hu⟩ : U) ∈ (⊥ : Subgroup U) := htop ▸ Subgroup.mem_top _
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  · apply le_normalizer_of_map_conj_le
    intro e he
    rintro _ ⟨_, ⟨_, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    set g : Subgroup.normalizer (L : Set G) := ⟨e, hEN he⟩ with hg
    set l' : L := L.normalizerMonoidHom g (q : L) with hl'
    have hl'H : l' ∈ H := by
      show ψ l' ∈ U
      have h1 : ψ l' = ggLAut L θ g (ψ q) := by
        rw [ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]
      rw [h1]
      exact hEU e he _ q.2
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨q, hq⟩
    have hqk : (q : L) ^ 2 ^ k = 1 := by
      have := congrArg (fun z : (P : Subgroup H) => ((z : H) : L)) hk
      simpa using this
    have hl'P : (⟨l', hl'H⟩ : H) ∈ (P : Subgroup H) := by
      refine hmemP _ k (Subtype.ext ?_)
      show l' ^ 2 ^ k = 1
      rw [hl', ← map_pow, hqk, map_one]
    exact ⟨l', ⟨⟨l', hl'H⟩, hl'P, rfl⟩, rfl⟩

end TwoLift

@[expose] def GGBstarBound (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ Eb Eh : Subgroup (MulAut R), (Eb : Set (MulAut R)) ⊆ I → IsElemAbelian p Eb →
    p ^ r ≤ Nat.card Eb → p ^ 3 ≤ Nat.card Eb → Eb ≤ Eh → IsElemAbelian p Eh →
    p ^ 2 * Nat.card Eb ≤ Nat.card Eh →
    ∃ E' : Subgroup (MulAut R), Eb < E' ∧ E' ≤ Eh ∧
      ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ φ ∈ E', ∀ u ∈ U, φ u ∈ U

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_bstarBound {p r : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G}
    {L : Subgroup G} (hS : LargeEvenSStar p B x L) (h4 : 4 ≤ LargeEvenTwoLocalRank p G)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S) (hL : commutator L = ⊤)
    {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (h3 : ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hbound : GGBstarBound p r R I) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hBE : B ≤ E) : Nat.card E ≤ p * Nat.card B := by
  have := Fact.mk hp
  have hEC : E ≤ Subgroup.centralizer ({x} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (IsElemAbelian.comm hE he (hBE hS.2.1))
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := fun e he =>
    mem_normalizer_of_sstar hS hnc (hEC he)
  set βB := ggBeta L θ hBN with hβB
  set βE := ggBeta L θ hEN with hβE
  have hBEr : βB.range ≤ βE.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBE b.2⟩, rfl⟩
  have hcB := card_range_ggBeta_mul L θ hp hS hL hBN
  have hcE := card_range_ggBeta_mul_of hp hE (hBE hS.2.1) hS.2.2.1 hS.2.2.2.1.1 hS.2.2.2.2 hL θ
    hEN
  have hEbI : (βB.range : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨b, rfl⟩
    exact ggBeta_mem L θ hBN h3 b
  have hEbA : IsElemAbelian p βB.range := isElemAbelian_range
    (fun a b => Subtype.ext (IsElemAbelian.comm hS.1.1 a.2 b.2))
    (fun a => Subtype.ext (by simpa using hS.1.1.2 a a.2)) βB
  have hEhA : IsElemAbelian p βE.range := isElemAbelian_range
    (fun a b => Subtype.ext (IsElemAbelian.comm hE a.2 b.2))
    (fun a => Subtype.ext (by simpa using hE.2 a a.2)) βE
  have hr : p ^ r ≤ Nat.card βB.range := pow_le_card_range_ggBeta hp hS hL θ hBN hlift
  have h3' : p ^ 3 ≤ Nat.card βB.range := by
    have h := pow_four_le_card_of_bmax hp hS.1 h4
    rw [← hcB, pow_succ] at h
    exact Nat.le_of_mul_le_mul_right h hp.pos
  by_contra hcon'
  have hcon := not_le.mp hcon'
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hE)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_of_isElemAbelian hS.1.1)
  have hp2 : p ^ 2 * Nat.card βB.range ≤ Nat.card βE.range := by
    have h1 : p ^ (m + 1) < p ^ e := by
      rw [← he, pow_succ, ← hm, mul_comm]
      exact hcon
    have hme : m + 2 ≤ e := by
      have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp h1
      omega
    have h5 : p ^ 2 * Nat.card B ≤ Nat.card E := by
      rw [hm, he, ← pow_add]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    rw [← hcB, ← hcE] at h5
    have h6 : p ^ 2 * Nat.card βB.range * p ≤ Nat.card βE.range * p := by
      calc p ^ 2 * Nat.card βB.range * p = p ^ 2 * (Nat.card βB.range * p) := by ring
        _ ≤ _ := h5
    exact Nat.le_of_mul_le_mul_right h6 hp.pos
  obtain ⟨E', hlt, hle, U, hU, hU2, hEU⟩ := hbound _ _ hEbI hEbA hr h3' hBEr hEhA hp2
  set E₂ : Subgroup G := (E'.comap βE).map E.subtype with hE₂
  have hE₂E : E₂ ≤ E := Subgroup.map_subtype_le _
  have hBE₂ : B ≤ E₂ := by
    intro b hb
    exact ⟨⟨b, hBE hb⟩, hlt.le ⟨⟨b, hb⟩, rfl⟩, rfl⟩
  have hBlt : B ≠ E₂ := by
    intro heq
    obtain ⟨φ, hφE', hφB⟩ := IsConcreteLE.exists_of_lt hlt
    obtain ⟨e₀, rfl⟩ := hle hφE'
    apply hφB
    have he₂ : (e₀ : G) ∈ E₂ := ⟨e₀, hφE', rfl⟩
    rw [← heq] at he₂
    exact ⟨⟨e₀, he₂⟩, rfl⟩
  have hE₂A : IsElemAbelian p E₂ := isElemAbelian_mono hE hE₂E
  obtain ⟨T, hT, hT2, hE₂T⟩ := exists_twoSubgroup_of_normalizes θ (hE₂E.trans hEN) hU hU2 (by
    intro e₁ he₁ u hu
    obtain ⟨e', he', rfl⟩ := id he₁
    exact hEU _ he' u hu)
  have hcard := card_le_of_twoLocal hp ⟨T, hT, hT2, rfl⟩ hE₂T hE₂A
  rw [← hS.1.2.1] at hcard
  exact hBlt (Subgroup.eq_of_le_of_card_ge hBE₂ hcard)

omit [Finite G] in
theorem isElemAbelian_zpowers {p : ℕ} {g : G} (hg : g ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers g) := CFSG.Open.isElemAbelian_zpowers hg

theorem exists_ggBstar_of_card_le {p : ℕ} {B : Subgroup G} (hB : IsElemAbelian p B)
    (hbound : ∀ E : Subgroup G, IsElemAbelian p E → B ≤ E → Nat.card E ≤ p * Nat.card B) :
    ∃ Bs : Subgroup G, GGBstar p B Bs := by
  have hfin : ({E : Subgroup G | IsElemAbelian p E ∧ B ≤ E} : Set (Subgroup G)).Finite :=
    Set.toFinite _
  obtain ⟨Bs, hBsS, hmax⟩ := Finset.exists_max_image hfin.toFinset (fun E => Nat.card E)
    ⟨B, (Set.Finite.mem_toFinset hfin).mpr ⟨hB, le_rfl⟩⟩
  obtain ⟨hBs, hBBs⟩ := (Set.Finite.mem_toFinset hfin).mp hBsS
  refine ⟨Bs, hBBs, hBs, hbound Bs hBs hBBs, ?_⟩
  intro g hg hgp
  have hcomm : ∀ a ∈ Bs, ∀ c ∈ Subgroup.zpowers g, a * c = c * a := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hg a ha) k)
  have hgA := isElemAbelian_sup hBs (isElemAbelian_zpowers hgp) hcomm
  have hle : Bs ≤ Bs ⊔ Subgroup.zpowers g := le_sup_left
  have hc := hmax _ ((Set.Finite.mem_toFinset hfin).mpr ⟨hgA, hBBs.trans hle⟩)
  have heq := Subgroup.eq_of_le_of_card_ge hle hc
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

theorem ggBstarInput_of_labels (ha₀ : GGLNoncyclicInput)
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I) :
    GGBstarInput := by
  intro G _ _ p B x L hT
  have hnc := ha₀ G p B x L hT
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hT
  have hp : p.Prime := hβ.1
  have hM := largeEvenMarking_and_labelAll (S := fun lab => LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hst.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBN, h3⟩, r, hlift, hbound⟩ := largeEvenRawDatum_exists hraw
  exact exists_ggBstar_of_card_le hS.1.1 fun E hE hBE =>
    card_le_of_bstarBound hp hS hβ.2.2.2 hnc hL θ hBN h3 hlift hbound hE hBE

end Reduction

end CFSG.StandardType
