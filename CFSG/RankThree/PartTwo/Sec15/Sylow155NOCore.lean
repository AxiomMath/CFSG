module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155KA6
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21GenA6
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155NO

open CFSG.RankThree.PartTwo

section Abstract

variable {G : Type*} [Group G]

private theorem mem_normalizer_of_forall_mem [Finite G] {A : Subgroup G} {g : G}
    (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) : g ∈ Subgroup.normalizer (A : Set G) :=
  Subgroup.mem_normalizer_iff.2 fun x =>
    (Sylow155KA6.apply_mem_iff_of_finite (MulAut.conj g) hg x).symm

private theorem le_normalizer_of_commute [Finite G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
  mem_normalizer_of_forall_mem fun b hb => by
    rw [h a ha b hb, mul_inv_cancel_right]
    exact hb

private theorem card_sup_mul_card_inf [Finite G] {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 := Subgroup.normal_subgroupOf_of_le_normalizer hHK
  have h2 := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hHK
  have hq : Nat.card (↥(H ⊔ K) ⧸ K.subgroupOf (H ⊔ K)) = Nat.card (↥H ⧸ K.subgroupOf H) :=
    (Nat.card_congr e.toEquiv).symm
  have hs : Nat.card (K.subgroupOf (H ⊔ K)) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show K ≤ H ⊔ K from le_sup_right)).toEquiv
  have hs' : Nat.card (K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_left K H]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf (H ⊔ K)), hs, hq,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf H), hs']
  ring

private theorem exists_mul_of_mem_sup [Finite G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : G} (hy : y ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hB : B ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_commute fun b hb a ha => (h a ha b hb).symm
  have hy' : y ∈ ((A ⊔ B : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left A B hB] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  exact ⟨a, ha, b, hb, rfl⟩

private theorem conj_mem_left [Finite G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : G} (hy : y ∈ A ⊔ B) {a : G} (ha : a ∈ A) :
    y * a * y⁻¹ ∈ A := by
  obtain ⟨a', ha', b', hb', rfl⟩ := exists_mul_of_mem_sup h hy
  have h1 : b' * a = a * b' := (h a ha b' hb').symm
  have h2 : a' * b' * a * (a' * b')⁻¹ = a' * a * a'⁻¹ := by
    calc a' * b' * a * (a' * b')⁻¹ = a' * (b' * a) * b'⁻¹ * a'⁻¹ := by group
      _ = a' * (a * b') * b'⁻¹ * a'⁻¹ := by rw [h1]
      _ = a' * a * a'⁻¹ := by group
  rw [h2]
  exact A.mul_mem (A.mul_mem ha' ha) (A.inv_mem ha')

private theorem conj_mem_right [Finite G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : G} (hy : y ∈ A ⊔ B) {b : G} (hb : b ∈ B) :
    y * b * y⁻¹ ∈ B :=
  conj_mem_left (A := B) (B := A) (fun b hb a ha => (h a ha b hb).symm) (by rwa [sup_comm]) hb

end Abstract

section Gamma

variable {Γ : Type*} [Group Γ]

private theorem card_subgroupOf_eq (A T : Subgroup Γ) :
    Nat.card (A.subgroupOf T) = Nat.card ↥(A ⊓ T) := by
  have h := Subgroup.card_subtype T (A.subgroupOf T)
  rw [Subgroup.subgroupOf_map_subtype] at h
  exact h.symm

private theorem card_ker_inf_mul_card_map {Q : Type*} [Group Q] (π : Γ →* Q) (T : Subgroup Γ) :
    Nat.card ↥(π.ker ⊓ T) * Nat.card (T.map π) = Nat.card T := by
  rw [← card_subgroupOf_eq, ← Subgroup.relIndex_ker]
  exact Subgroup.card_mul_index _

private theorem card_eq_sixty_mul {T K : Subgroup Γ} (hKT : K ≤ T)
    (f : ↥T →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hker : f.ker = K.subgroupOf T) : Nat.card T = 60 * Nat.card K := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective hf
  have h2 : Nat.card f.ker = Nat.card K := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKT).toEquiv
  have h3 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [h2, h3] at h1
  omega

private theorem card_map_eq_sixty_mul [Finite Γ] {Q : Type*} [Group Q] (π : Γ →* Q)
    {T K : Subgroup Γ} (hKT : K ≤ T) (hTπ : T ⊓ π.ker ≤ K) (hT : Nat.card T = 60 * Nat.card K) :
    Nat.card (T.map π) = 60 * Nat.card (K.map π) := by
  have hker : π.ker ⊓ T = π.ker ⊓ K :=
    le_antisymm (fun x hx => ⟨hx.1, hTπ ⟨hx.2, hx.1⟩⟩) (inf_le_inf_left _ hKT)
  have h1 := card_ker_inf_mul_card_map π T
  have h2 := card_ker_inf_mul_card_map π K
  rw [hker] at h1
  have hc : 0 < Nat.card ↥(π.ker ⊓ K) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hc
  calc Nat.card ↥(π.ker ⊓ K) * Nat.card (T.map π) = Nat.card T := h1
    _ = 60 * Nat.card K := hT
    _ = 60 * (Nat.card ↥(π.ker ⊓ K) * Nat.card (K.map π)) := by rw [h2]
    _ = Nat.card ↥(π.ker ⊓ K) * (60 * Nat.card (K.map π)) := by ring

private theorem conj_mem_of_ker {T K : Subgroup Γ} (hKT : K ≤ T) {B : Type*} [Group B]
    (f : ↥T →* B) (hker : f.ker = K.subgroupOf T) {t k : Γ} (ht : t ∈ T) (hk : k ∈ K) :
    t * k * t⁻¹ ∈ K := by
  have hkT : k ∈ T := hKT hk
  have h1 : (⟨k, hkT⟩ : ↥T) ∈ f.ker := by
    rw [hker]
    exact hk
  have h2 : (⟨t * k * t⁻¹, T.mul_mem (T.mul_mem ht hkT) (T.inv_mem ht)⟩ : ↥T) ∈ f.ker := by
    have h3 : (⟨t * k * t⁻¹, T.mul_mem (T.mul_mem ht hkT) (T.inv_mem ht)⟩ : ↥T) =
        ⟨t, ht⟩ * ⟨k, hkT⟩ * ⟨t, ht⟩⁻¹ := rfl
    rw [MonoidHom.mem_ker, h3, map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 h1, mul_one,
      mul_inv_cancel]
  rw [hker] at h2
  exact h2

private theorem le_or_sup_eq {Q : Type*} [Group Q] (π : Γ →* Q) {T K : Subgroup Γ} (hKT : K ≤ T)
    (f : ↥T →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hker : f.ker = K.subgroupOf T) {L : Subgroup Q} (hLS : L ≤ T.map π)
    (hLn : ∀ s ∈ T.map π, ∀ l ∈ L, s * l * s⁻¹ ∈ L) :
    L ≤ K.map π ∨ L ⊔ K.map π = T.map π := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  set L' : Subgroup ↥T := L.comap (π.comp T.subtype) with hL'
  have hmem : ∀ t : ↥T, t ∈ L' ↔ π t ∈ L := fun t => Iff.rfl
  haveI hL'n : L'.Normal := ⟨fun a ha g => by
    rw [hmem] at ha ⊢
    have h1 : π g ∈ T.map π := ⟨g, g.2, rfl⟩
    have := hLn (π g) h1 (π a) ha
    simpa [map_mul, map_inv] using this⟩
  haveI : (L'.map f).Normal := hL'n.map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L'.map f) with hb | ht
  · left
    have hle : L' ≤ f.ker := (Subgroup.map_eq_bot_iff _).1 hb
    rw [hker] at hle
    intro l hl
    obtain ⟨t, htT, rfl⟩ := hLS hl
    exact ⟨t, hle (show (⟨t, htT⟩ : ↥T) ∈ L' from hl), rfl⟩
  · right
    refine le_antisymm (sup_le hLS (Subgroup.map_mono hKT)) ?_
    rintro _ ⟨t, htT, rfl⟩
    have h1 : f ⟨t, htT⟩ ∈ L'.map f := by
      rw [ht]
      exact Subgroup.mem_top _
    obtain ⟨l', hl', hl'f⟩ := h1
    have h2 : l'⁻¹ * ⟨t, htT⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hl'f, inv_mul_cancel]
    rw [hker] at h2
    have h3 : (↑l' : Γ)⁻¹ * t ∈ K := h2
    have h4 : π t = π l' * π ((↑l' : Γ)⁻¹ * t) := by simp
    rw [h4]
    exact Subgroup.mul_mem_sup hl' ⟨_, h3, rfl⟩

end Gamma

section KA6

private theorem exists_mulAut_conj {G : Type*} [Group G] [Finite G] (J : Subgroup G) (d : G)
    (hd : ∀ x ∈ J, d * x * d⁻¹ ∈ J) : ∃ σ : MulAut ↥J, ∀ x : ↥J, (σ x : G) = d * x * d⁻¹ := by
  let f : ↥J →* ↥J := ((MulAut.conj d).toMonoidHom.comp J.subtype).codRestrict J fun x => hd x x.2
  have hinj : Function.Injective f := fun a b h =>
    Subtype.ext ((MulAut.conj d).injective (congrArg Subtype.val h))
  exact ⟨MulEquiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩, fun x => rfl⟩

private theorem card_map_mk_mul {X : Type*} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    {P : Subgroup X} (hZP : Z ≤ P) :
    Nat.card (P.map (QuotientGroup.mk' Z)) * Nat.card Z = Nat.card P := by
  have hidx : (P.map (QuotientGroup.mk' Z)).index = P.index :=
    Subgroup.index_map_eq P (QuotientGroup.mk'_surjective Z)
      (by rw [QuotientGroup.ker_mk']; exact hZP)
  have h1 := Subgroup.card_mul_index (P.map (QuotientGroup.mk' Z))
  have h2 := Subgroup.card_mul_index P
  have h3 := Z.card_eq_card_quotient_mul_card_subgroup
  rw [hidx] at h1
  have hpos : 0 < P.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc Nat.card (P.map (QuotientGroup.mk' Z)) * Nat.card Z * P.index
      = (Nat.card (P.map (QuotientGroup.mk' Z)) * P.index) * Nat.card Z := by ring
    _ = Nat.card (X ⧸ Z) * Nat.card Z := by rw [h1]
    _ = Nat.card X := h3.symm
    _ = Nat.card P * P.index := h2.symm

variable {Q : Type} [Group Q] [Finite Q]

private theorem exists_inner_mod_center {J P : Subgroup Q}
    (hperf : commutator ↥J = ⊤) (hT : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6)))
    (hPJ : P ≤ J)
    (hP60 : Nat.card ((P.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J))) = 60)
    {d : Q} (hdJ : ∀ x ∈ J, d * x * d⁻¹ ∈ J) (hdP : ∀ x ∈ P, d * x * d⁻¹ ∈ P)
    (hdZ : ∀ z ∈ Sec14.Item148PtRes.centerIn J, d * z * d⁻¹ = z) :
    ∃ p ∈ P, ∀ y ∈ P,
      (d * y * d⁻¹)⁻¹ * (p * y * p⁻¹) ∈ Sec14.Item148PtRes.centerIn J := by
  have h1080 := Sec14.Item148PtRes.card_eq_of_isTripleCover hT
  obtain ⟨hZ, ⟨e⟩⟩ := hT
  obtain ⟨ψ⟩ := QuasithinUnique.Out21.A6.exists_psl29_equiv
  obtain ⟨σ, hσ⟩ := exists_mulAut_conj J d hdJ
  have hσZ : ∀ z ∈ Subgroup.center ↥J, σ z = z := fun z hz =>
    Subtype.ext (by
      rw [hσ]
      exact hdZ z (Subgroup.mem_map.2 ⟨z, hz, rfl⟩))
  have hZmap : (Subgroup.center ↥J).map (σ : ↥J →* ↥J) = Subgroup.center ↥J := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h : σ y = y := hσZ y hy
      show σ y ∈ _
      rw [h]
      exact hy
    · intro hx
      exact ⟨x, hx, hσZ x hx⟩
  let σ' : MulAut (↥J ⧸ Subgroup.center ↥J) := QuotientGroup.congr _ _ σ hZmap
  have hσ' : ∀ q : ↥J, σ' (QuotientGroup.mk q) = QuotientGroup.mk (σ q) := fun q => rfl
  have hσH : ∀ y ∈ (P.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)),
      σ' y ∈ (P.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)) := by
    rintro _ ⟨y₀, hy₀, rfl⟩
    refine ⟨σ y₀, ?_, rfl⟩
    have hy₀' : y₀ ∈ P.subgroupOf J := hy₀
    show σ y₀ ∈ P.subgroupOf J
    rw [Subgroup.mem_subgroupOf, hσ]
    exact hdP _ (Subgroup.mem_subgroupOf.1 hy₀')
  obtain ⟨_, ⟨q₀, hq₀, rfl⟩, hh⟩ :=
    Sylow155KA6.exists_inner_of_fixes_center hperf hZ h1080 (e.trans ψ.symm) hσZ hσ' hP60 hσH
  refine ⟨q₀, Subgroup.mem_subgroupOf.1 hq₀, fun y hy => ?_⟩
  have hyJ : y ∈ J := hPJ hy
  have hy₀ : (⟨y, hyJ⟩ : ↥J) ∈ P.subgroupOf J := Subgroup.mem_subgroupOf.2 hy
  have h2 : (QuotientGroup.mk (σ ⟨y, hyJ⟩) : ↥J ⧸ Subgroup.center ↥J) =
      QuotientGroup.mk (q₀ * ⟨y, hyJ⟩ * q₀⁻¹) :=
    hh (QuotientGroup.mk' _ ⟨y, hyJ⟩) ⟨_, hy₀, rfl⟩
  have h3 := QuotientGroup.eq.1 h2
  have h4 : (((σ ⟨y, hyJ⟩)⁻¹ * (q₀ * ⟨y, hyJ⟩ * q₀⁻¹) : ↥J) : Q) ∈
      Sec14.Item148PtRes.centerIn J := Subgroup.mem_map.2 ⟨_, h3, rfl⟩
  have h5 : (((σ ⟨y, hyJ⟩)⁻¹ * (q₀ * ⟨y, hyJ⟩ * q₀⁻¹) : ↥J) : Q) =
      (d * y * d⁻¹)⁻¹ * ((q₀ : Q) * y * (q₀ : Q)⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ]
  rw [← h5]
  exact h4

end KA6

section Core

variable {Q : Type} [Group Q] [Finite Q]

private theorem inf_le_or {J₁ J₂ S N : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥)
    (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3) (hSY : S ≤ J₁ ⊔ J₂)
    (hNn : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hN3 : ¬ 3 ∣ Nat.card N)
    (hSN : Nat.card S = 60 * Nat.card N)
    (hsimple : ∀ L : Subgroup Q, L ≤ S → (∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L) →
      L ≤ N ∨ L ⊔ N = S) :
    S ⊓ J₂ ≤ N ∨ S ⊓ J₁ ≤ N := by
  have hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := fun a ha b hb =>
    Sec14.Item148PtRes.commute_of_commutator_eq_bot hJ ha hb
  have hZc : ∀ z ∈ J₁ ⊓ J₂, ∀ y ∈ J₁ ⊔ J₂, y * z * y⁻¹ = z := by
    intro z hz y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm hy
    have h1 : z * b = b * z := hcomm z hz.1 b hb
    have h2 : a * z = z * a := hcomm a ha z hz.2
    calc a * b * z * (a * b)⁻¹ = a * (b * z) * b⁻¹ * a⁻¹ := by group
      _ = a * (z * b) * b⁻¹ * a⁻¹ := by rw [h1]
      _ = a * z * a⁻¹ := by group
      _ = z := by rw [h2]; group
  have hNnorm : ∀ A : Subgroup Q, A ≤ S → A ≤ Subgroup.normalizer (N : Set Q) :=
    fun A hA a ha => mem_normalizer_of_forall_mem fun n hn => hNn a (hA ha) n hn
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hSZ : S ⊓ (J₁ ⊓ J₂) = ⊥ := by
    set L := S ⊓ (J₁ ⊓ J₂) with hL
    have hLS : L ≤ S := inf_le_left
    have hLn : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L := fun s hs l hl => by
      rw [hZc l hl.2 s (hSY hs)]
      exact hl
    have hL3 : Nat.card L ∣ 3 := h3 ▸ Subgroup.card_dvd_of_le (inf_le_right : L ≤ J₁ ⊓ J₂)
    rcases hsimple L hLS hLn with hLN | hLN
    · have hL1 : Nat.card L ∣ Nat.card N := Subgroup.card_dvd_of_le hLN
      rcases (Nat.dvd_prime Nat.prime_three).1 hL3 with h | h
      · exact Subgroup.eq_bot_of_card_eq _ h
      · exact absurd (h ▸ hL1) hN3
    · exfalso
      have h1 := card_sup_mul_card_inf (hNnorm L hLS)
      rw [hLN] at h1
      have h2 : Nat.card L ≤ 3 := Nat.le_of_dvd (by norm_num) hL3
      have h3' : 0 < Nat.card ↥(L ⊓ N) := Nat.card_pos
      have e1 : Nat.card S ≤ Nat.card S * Nat.card ↥(L ⊓ N) := Nat.le_mul_of_pos_right _ h3'
      have e2 : Nat.card L * Nat.card N ≤ 3 * Nat.card N := Nat.mul_le_mul_right _ h2
      omega
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h2N, h1N⟩ := hcon
  have hA₁n : ∀ s ∈ S, ∀ a ∈ S ⊓ J₁, s * a * s⁻¹ ∈ S ⊓ J₁ := fun s hs a ha =>
    ⟨S.mul_mem (S.mul_mem hs ha.1) (S.inv_mem hs), conj_mem_left hcomm (hSY hs) ha.2⟩
  have hA₂n : ∀ s ∈ S, ∀ a ∈ S ⊓ J₂, s * a * s⁻¹ ∈ S ⊓ J₂ := fun s hs a ha =>
    ⟨S.mul_mem (S.mul_mem hs ha.1) (S.inv_mem hs), conj_mem_right hcomm (hSY hs) ha.2⟩
  have hs₁ : (S ⊓ J₁) ⊔ N = S := (hsimple _ inf_le_left hA₁n).resolve_left h1N
  have hs₂ : (S ⊓ J₂) ⊔ N = S := (hsimple _ inf_le_left hA₂n).resolve_left h2N
  have hdiv : ∀ A : Subgroup Q, A ≤ S → A ⊔ N = S → ∀ a : ℕ, 3 ^ a ∣ Nat.card S →
      3 ^ a ∣ Nat.card A := by
    intro A hAS hAN a ha
    have h1 := card_sup_mul_card_inf (hNnorm A hAS)
    rw [hAN] at h1
    have h2 : 3 ^ a ∣ Nat.card A * Nat.card N := h1 ▸ ha.mul_right _
    have hcop : Nat.Coprime (3 ^ a) (Nat.card N) :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3)
    exact hcop.dvd_of_dvd_mul_right h2
  have hA12 : (S ⊓ J₁) ⊓ (S ⊓ J₂) = ⊥ := by
    refine eq_bot_iff.2 (le_trans (fun x hx => ?_) hSZ.le)
    exact ⟨hx.1.1, hx.1.2, hx.2.2⟩
  have hA1norm : S ⊓ J₁ ≤ Subgroup.normalizer ((S ⊓ J₂ : Subgroup Q) : Set Q) :=
    le_normalizer_of_commute fun a ha b hb => hcomm a ha.2 b hb.2
  have hprod := card_sup_mul_card_inf hA1norm
  rw [hA12, Subgroup.card_bot, mul_one] at hprod
  have hsup : Nat.card ↥((S ⊓ J₁) ⊔ (S ⊓ J₂)) ∣ Nat.card S :=
    Subgroup.card_dvd_of_le (sup_le inf_le_left inf_le_left)
  rw [hprod] at hsup
  have hSne : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have hpow : 3 ^ padicValNat 3 (Nat.card S) ∣ Nat.card S := pow_padicValNat_dvd
  have h3a₁ := hdiv _ inf_le_left hs₁ _ hpow
  have h3a₂ := hdiv _ inf_le_left hs₂ _ hpow
  have h33 : 3 ^ (padicValNat 3 (Nat.card S) + padicValNat 3 (Nat.card S)) ∣ Nat.card S := by
    rw [pow_add]
    exact (Nat.mul_dvd_mul h3a₁ h3a₂).trans hsup
  have hle : padicValNat 3 (Nat.card S) + padicValNat 3 (Nat.card S) ≤
      padicValNat 3 (Nat.card S) := (padicValNat_dvd_iff_le hSne).1 h33
  have h3S : 3 ∣ Nat.card S := by
    rw [hSN]
    exact Dvd.dvd.mul_right (by norm_num) _
  have h1le : 1 ≤ padicValNat 3 (Nat.card S) :=
    (padicValNat_dvd_iff_le hSne).1 (by simpa using h3S)
  omega

private theorem core_of_left {J₁ J₂ S N : Subgroup Q}
    (hperf₁ : commutator ↥J₁ = ⊤) (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hJ : ⁅J₁, J₂⁆ = ⊥) (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3) (hSY : S ≤ J₁ ⊔ J₂)
    (hN3 : ¬ 3 ∣ Nat.card N) (hSN : Nat.card S = 60 * Nat.card N) (hS2 : S ⊓ J₂ ≤ N)
    {d : Q} (hdS : ∀ x ∈ S, d * x * d⁻¹ ∈ S) (hdJ₁ : ∀ x ∈ J₁, d * x * d⁻¹ ∈ J₁)
    (hdJ₂ : ∀ x ∈ J₂, d * x * d⁻¹ ∈ J₂) (hdZ : ∀ z ∈ J₁ ⊓ J₂, d * z * d⁻¹ = z) :
    ∃ s ∈ S, ∀ x ∈ S, (d * x * d⁻¹) * (s * x * s⁻¹)⁻¹ ∈ N := by
  have hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := fun a ha b hb =>
    Sec14.Item148PtRes.commute_of_commutator_eq_bot hJ ha hb
  have h1080 := Sec14.Item148PtRes.card_eq_of_isTripleCover hT₁
  have hZc : Nat.card (Subgroup.center ↥J₁) = 3 := hT₁.1
  obtain ⟨e⟩ := hT₁.2
  have hZeq : J₁ ⊓ J₂ = Sec14.Item148PtRes.centerIn J₁ :=
    Sec14.Item148PtRes.inf_eq_centerIn_left hJ h3 hZc
  have hJ₂pos : 0 < Nat.card J₂ := Nat.card_pos
  set P : Subgroup Q := (S ⊔ J₂) ⊓ J₁ with hP
  have hPJ₁ : P ≤ J₁ := inf_le_right
  have hS₂ : S ≤ Subgroup.normalizer (J₂ : Set Q) := fun s hs =>
    mem_normalizer_of_forall_mem fun b hb => conj_mem_right hcomm (hSY hs) hb
  have hP₂ : P ≤ Subgroup.normalizer (J₂ : Set Q) :=
    le_normalizer_of_commute fun a ha b hb => hcomm a (hPJ₁ ha) b hb
  have hPsup : P ⊔ J₂ = S ⊔ J₂ := by
    refine le_antisymm (sup_le inf_le_left le_sup_right) (sup_le (fun s hs => ?_) le_sup_right)
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcomm (hSY hs)
    have haP : a ∈ P := by
      refine ⟨?_, ha⟩
      have h1 : a * b * b⁻¹ ∈ S ⊔ J₂ :=
        (S ⊔ J₂).mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right (J₂.inv_mem hb))
      simpa using h1
    exact Subgroup.mul_mem_sup haP hb
  have hPinf : P ⊓ J₂ = J₁ ⊓ J₂ :=
    le_antisymm (fun x hx => ⟨hPJ₁ hx.1, hx.2⟩)
      (fun x hx => ⟨⟨Subgroup.mem_sup_right hx.2, hx.1⟩, hx.2⟩)
  have hf1 := card_sup_mul_card_inf hP₂
  have hf2 := card_sup_mul_card_inf hS₂
  rw [hPsup, hPinf, h3] at hf1
  have hPS : Nat.card P * Nat.card ↥(S ⊓ J₂) = 3 * Nat.card S := by
    apply Nat.eq_of_mul_eq_mul_right hJ₂pos
    calc Nat.card P * Nat.card ↥(S ⊓ J₂) * Nat.card J₂
        = (Nat.card P * Nat.card J₂) * Nat.card ↥(S ⊓ J₂) := by ring
      _ = (Nat.card ↥(S ⊔ J₂) * 3) * Nat.card ↥(S ⊓ J₂) := by rw [← hf1]
      _ = 3 * (Nat.card ↥(S ⊔ J₂) * Nat.card ↥(S ⊓ J₂)) := by ring
      _ = 3 * (Nat.card S * Nat.card J₂) := by rw [hf2]
      _ = 3 * Nat.card S * Nat.card J₂ := by ring
  have hZP : Subgroup.center ↥J₁ ≤ P.subgroupOf J₁ := by
    intro z hz
    have hz' : (z : Q) ∈ J₁ ⊓ J₂ := by
      rw [hZeq]
      exact Subgroup.mem_map.2 ⟨z, hz, rfl⟩
    exact Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_sup_right hz'.2, z.2⟩
  have hcardH := card_map_mk_mul (Subgroup.center ↥J₁) hZP
  have hP'card : Nat.card (P.subgroupOf J₁) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPJ₁).toEquiv
  rw [hP'card, hZc] at hcardH
  have hHS : Nat.card ((P.subgroupOf J₁).map (QuotientGroup.mk' (Subgroup.center ↥J₁))) *
      Nat.card ↥(S ⊓ J₂) = Nat.card S := by
    have : 3 * (Nat.card ((P.subgroupOf J₁).map (QuotientGroup.mk' (Subgroup.center ↥J₁))) *
        Nat.card ↥(S ⊓ J₂)) = 3 * Nat.card S := by
      rw [← hPS, ← hcardH]
      ring
    omega
  obtain ⟨m, hm⟩ := (Subgroup.card_dvd_of_le hS2 : Nat.card ↥(S ⊓ J₂) ∣ Nat.card N)
  have hcpos : 0 < Nat.card ↥(S ⊓ J₂) := Nat.card_pos
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hH60m : Nat.card ((P.subgroupOf J₁).map (QuotientGroup.mk' (Subgroup.center ↥J₁))) =
      60 * m := by
    apply Nat.eq_of_mul_eq_mul_right hcpos
    calc Nat.card ((P.subgroupOf J₁).map (QuotientGroup.mk' (Subgroup.center ↥J₁))) *
          Nat.card ↥(S ⊓ J₂) = Nat.card S := hHS
      _ = 60 * Nat.card N := hSN
      _ = 60 * (Nat.card ↥(S ⊓ J₂) * m) := by rw [← hm]
      _ = 60 * m * Nat.card ↥(S ⊓ J₂) := by ring
  have h3m : ¬ 3 ∣ m := fun h => hN3 (h.trans (Dvd.intro_left _ hm.symm))
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun h => by
    rw [h, mul_zero] at hm
    omega
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (↥J₁ ⧸ Subgroup.center ↥J₁) := e.isSimpleGroup
  have hcardQ : Nat.card (↥J₁ ⧸ Subgroup.center ↥J₁) = 360 := by
    have h := (Subgroup.center ↥J₁).card_eq_card_quotient_mul_card_subgroup
    rw [h1080, hZc] at h
    omega
  have hHtop : (P.subgroupOf J₁).map (QuotientGroup.mk' (Subgroup.center ↥J₁)) ≠ ⊤ := by
    intro htop
    have h360 : Nat.card ((P.subgroupOf J₁).map (QuotientGroup.mk' (Subgroup.center ↥J₁))) =
        360 := by
      rw [htop, Subgroup.card_top, hcardQ]
    exact h3m ⟨2, by omega⟩
  have hle := Sylow155KA6.card_le_sixty hcardQ hHtop
  have hH60 : Nat.card ((P.subgroupOf J₁).map (QuotientGroup.mk' (Subgroup.center ↥J₁))) = 60 := by
    omega
  have hdSJ : ∀ w ∈ S ⊔ J₂, d * w * d⁻¹ ∈ S ⊔ J₂ := by
    intro w hw
    have hw' : w ∈ ((S ⊔ J₂ : Subgroup Q) : Set Q) := hw
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S J₂ hS₂] at hw'
    obtain ⟨s, hs, j, hj, rfl⟩ := hw'
    have h1 : d * (s * j) * d⁻¹ = (d * s * d⁻¹) * (d * j * d⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem_sup (hdS s hs) (hdJ₂ j hj)
  have hdP : ∀ x ∈ P, d * x * d⁻¹ ∈ P := fun x hx => ⟨hdSJ x hx.1, hdJ₁ x hx.2⟩
  obtain ⟨p, hpP, hp⟩ := exists_inner_mod_center hperf₁ hT₁ hPJ₁ hH60 hdJ₁ hdP
    (fun z hz => hdZ z (by rw [hZeq]; exact hz))
  have hpSJ : p ∈ ((S ⊔ J₂ : Subgroup Q) : Set Q) := hpP.1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S J₂ hS₂] at hpSJ
  obtain ⟨s, hs, j, hj, hsj⟩ := hpSJ
  refine ⟨s, hs, fun x hx => ?_⟩
  obtain ⟨j₁, hj₁, j₂, hj₂, rfl⟩ := exists_mul_of_mem_sup hcomm (hSY hx)
  have hj₁P : j₁ ∈ P := by
    refine ⟨?_, hj₁⟩
    have h1 : j₁ * j₂ * j₂⁻¹ ∈ S ⊔ J₂ :=
      (S ⊔ J₂).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right (J₂.inv_mem hj₂))
    simpa using h1
  have hz := hp j₁ hj₁P
  rw [← hZeq] at hz
  have hpj : p * j₁ * p⁻¹ = s * j₁ * s⁻¹ := by
    rw [← hsj]
    have h1 : j * j₁ = j₁ * j := (hcomm j₁ hj₁ j hj).symm
    calc s * j * j₁ * (s * j)⁻¹ = s * (j * j₁) * j⁻¹ * s⁻¹ := by group
      _ = s * (j₁ * j) * j⁻¹ * s⁻¹ := by rw [h1]
      _ = s * j₁ * s⁻¹ := by group
  rw [hpj] at hz
  have ha₁ : d * j₁ * d⁻¹ ∈ J₁ := hdJ₁ j₁ hj₁
  have hu : (d * j₂ * d⁻¹) * (s * j₂ * s⁻¹)⁻¹ ∈ J₂ :=
    J₂.mul_mem (hdJ₂ j₂ hj₂) (J₂.inv_mem (conj_mem_right hcomm (hSY hs) hj₂))
  have hv : ((d * j₂ * d⁻¹) * (s * j₂ * s⁻¹)⁻¹) *
      ((d * j₁ * d⁻¹)⁻¹ * (s * j₁ * s⁻¹))⁻¹ ∈ J₂ := J₂.mul_mem hu (J₂.inv_mem hz.2)
  have hw : (d * (j₁ * j₂) * d⁻¹) * (s * (j₁ * j₂) * s⁻¹)⁻¹ =
      (d * j₁ * d⁻¹) * (((d * j₂ * d⁻¹) * (s * j₂ * s⁻¹)⁻¹) *
        ((d * j₁ * d⁻¹)⁻¹ * (s * j₁ * s⁻¹))⁻¹) * (d * j₁ * d⁻¹)⁻¹ := by group
  have hwJ₂ : (d * (j₁ * j₂) * d⁻¹) * (s * (j₁ * j₂) * s⁻¹)⁻¹ ∈ J₂ := by
    rw [hw, hcomm _ ha₁ _ hv, mul_inv_cancel_right]
    exact hv
  have hwS : (d * (j₁ * j₂) * d⁻¹) * (s * (j₁ * j₂) * s⁻¹)⁻¹ ∈ S :=
    S.mul_mem (hdS _ hx) (S.inv_mem (S.mul_mem (S.mul_mem hs hx) (S.inv_mem hs)))
  exact hS2 ⟨hwS, hwJ₂⟩

private theorem exists_inner_mod {J₁ J₂ S N : Subgroup Q}
    (hperf₁ : commutator ↥J₁ = ⊤) (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hperf₂ : commutator ↥J₂ = ⊤) (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6)))
    (hJ : ⁅J₁, J₂⁆ = ⊥) (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3) (hSY : S ≤ J₁ ⊔ J₂)
    (hNn : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hN3 : ¬ 3 ∣ Nat.card N)
    (hSN : Nat.card S = 60 * Nat.card N)
    (hsimple : ∀ L : Subgroup Q, L ≤ S → (∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L) →
      L ≤ N ∨ L ⊔ N = S)
    {d : Q} (hdS : ∀ x ∈ S, d * x * d⁻¹ ∈ S) (hdJ₁ : ∀ x ∈ J₁, d * x * d⁻¹ ∈ J₁)
    (hdJ₂ : ∀ x ∈ J₂, d * x * d⁻¹ ∈ J₂) (hdZ : ∀ z ∈ J₁ ⊓ J₂, d * z * d⁻¹ = z) :
    ∃ s ∈ S, ∀ x ∈ S, (d * x * d⁻¹) * (s * x * s⁻¹)⁻¹ ∈ N := by
  rcases inf_le_or hJ h3 hSY hNn hN3 hSN hsimple with h | h
  · exact core_of_left hperf₁ hT₁ hJ h3 hSY hN3 hSN h hdS hdJ₁ hdJ₂ hdZ
  · have hJ' : ⁅J₂, J₁⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hJ
    have h3' : Nat.card ↥(J₂ ⊓ J₁) = 3 := by rw [inf_comm]; exact h3
    exact core_of_left hperf₂ hT₂ hJ' h3' (by rwa [sup_comm]) hN3 hSN h hdS hdJ₂ hdJ₁
      fun z hz => hdZ z (by rwa [inf_comm])

end Core

theorem exists_inner_of_centralProduct {Γ Q : Type} [Group Γ] [Finite Γ] [Group Q] [Finite Q]
    (π : Γ →* Q) {J₁ J₂ : Subgroup Q}
    (hperf₁ : commutator ↥J₁ = ⊤) (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hperf₂ : commutator ↥J₂ = ⊤) (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6)))
    (hJ : ⁅J₁, J₂⁆ = ⊥) (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3)
    {T K : Subgroup Γ} (hKT : K ≤ T) (hK3 : ¬ 3 ∣ Nat.card K)
    (f : ↥T →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hker : f.ker = K.subgroupOf T) (hTπ : T ⊓ π.ker ≤ K) (hTJ : T.map π ≤ J₁ ⊔ J₂)
    {δ : Γ} (hδT : ∀ x ∈ T, δ * x * δ⁻¹ ∈ T)
    (hδJ₁ : ∀ x ∈ J₁, π δ * x * (π δ)⁻¹ ∈ J₁) (hδJ₂ : ∀ x ∈ J₂, π δ * x * (π δ)⁻¹ ∈ J₂)
    (hδZ : ∀ z ∈ J₁ ⊓ J₂, π δ * z * (π δ)⁻¹ = z) :
    ∃ t ∈ T, ∀ x ∈ T, (δ * x * δ⁻¹) * (t * x * t⁻¹)⁻¹ ∈ K := by
  have hT60 := card_eq_sixty_mul hKT f hf hker
  have hS60 := card_map_eq_sixty_mul π hKT hTπ hT60
  have hNn : ∀ s ∈ T.map π, ∀ n ∈ K.map π, s * n * s⁻¹ ∈ K.map π := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨k, hk, rfl⟩
    exact ⟨t * k * t⁻¹, conj_mem_of_ker hKT f hker ht hk, by simp⟩
  have hN3 : ¬ 3 ∣ Nat.card (K.map π) := fun h => hK3 (h.trans (Subgroup.card_map_dvd K π))
  have hdS : ∀ x ∈ T.map π, π δ * x * (π δ)⁻¹ ∈ T.map π := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨δ * t * δ⁻¹, hδT t ht, by simp⟩
  obtain ⟨s, hs, hsx⟩ := exists_inner_mod hperf₁ hT₁ hperf₂ hT₂ hJ h3 hTJ hNn hN3 hS60
    (fun L hLS hLn => le_or_sup_eq π hKT f hf hker hLS hLn) hdS hδJ₁ hδJ₂ hδZ
  obtain ⟨t, htT, rfl⟩ := hs
  refine ⟨t, htT, fun x hx => ?_⟩
  have hyT : (δ * x * δ⁻¹) * (t * x * t⁻¹)⁻¹ ∈ T :=
    T.mul_mem (hδT x hx) (T.inv_mem (T.mul_mem (T.mul_mem htT hx) (T.inv_mem htT)))
  have hπy : π ((δ * x * δ⁻¹) * (t * x * t⁻¹)⁻¹) ∈ K.map π := by
    have h1 := hsx (π x) ⟨x, hx, rfl⟩
    simpa only [map_mul, map_inv] using h1
  obtain ⟨k, hk, hπk⟩ := hπy
  have hkker : k⁻¹ * ((δ * x * δ⁻¹) * (t * x * t⁻¹)⁻¹) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπk, inv_mul_cancel]
  have hk' : k⁻¹ * ((δ * x * δ⁻¹) * (t * x * t⁻¹)⁻¹) ∈ T ⊓ π.ker :=
    ⟨T.mul_mem (T.inv_mem (hKT hk)) hyT, hkker⟩
  have h2 := K.mul_mem hk (hTπ hk')
  simpa using h2

end CFSG.RankThree.PartTwo.Sec15.Sylow155NO
