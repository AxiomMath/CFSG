module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NinePieces
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Cent
public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvPow
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTGroup
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

theorem twoLocalPrimeRank_centralizer_le_five {G : Type} [Group G] [Finite G]
    {b₀ : G} {K : Subgroup G} (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥) (hmark : IsTwD5 K)
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hsup : Subgroup.centralizer ({b₀} : Set G) =
      K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)))
    (hDodd : Odd (Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G))))
    (hT5 : T5TwoLocalK) :
    twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({b₀} : Set G)) ≤ 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Subgroup.centralizer ({b₀} : Set G)
  let D : Subgroup G := C ⊓ Subgroup.centralizer (K : Set G)
  let KC : Subgroup ↥C := K.subgroupOf C
  have hKCn : KC.Normal := hKn
  have hKC' : K ≤ C := hKC
  have hDC : D ≤ C := inf_le_left
  have hDK : D ≤ Subgroup.centralizer (K : Set G) := inf_le_right
  have hKDbot : K ⊓ D = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxK, hxD⟩ := Subgroup.mem_inf.mp hx
    have hxCK : x ∈ Subgroup.centralizer (K : Set G) := hDK hxD
    have hxcen : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxCK (y : G) y.2)
    rw [hKz, Subgroup.mem_bot] at hxcen
    exact Subtype.ext_iff.mp hxcen
  have hcomm : ∀ a ∈ K, ∀ b ∈ D, Commute a b := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hDK hb) a ha
  have hcardC : Nat.card ↥C = Nat.card K * Nat.card ↥D := by
    have h := CFSG.card_sup_eq_mul_of_commute K D hcomm hKDbot
    rwa [← hsup] at h
  have hcardKC : Nat.card KC = Nat.card K := by
    have h := Subgroup.card_map_of_injective (Subgroup.subtype_injective C) (K := KC)
    rw [Subgroup.map_subgroupOf_eq_of_le hKC'] at h
    exact h.symm
  have hcardQuot : Nat.card (↥C ⧸ KC) = Nat.card ↥D := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup KC
    rw [hcardC, hcardKC, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h.symm
  have hoddQuot : Odd (Nat.card (↥C ⧸ KC)) := hcardQuot ▸ hDodd
  refine fs81Nt_twoLocalPrimeRank_le (G := ↥C) (m := 5) ?_
  intro H hH
  obtain ⟨P, hPbot, hP2, rfl⟩ := hH
  refine fs81Nt_pRank_le (G := ↥C) (H := Subgroup.normalizer (P : Set ↥C)) (m := 5) ?_
  intro F hF hFea
  have hPle : P ≤ KC := by
    have hoddIdx : Odd KC.index := by
      rw [Subgroup.index_eq_card]
      exact hoddQuot
    obtain ⟨n, hn⟩ := (hP2.map (QuotientGroup.mk' KC)).exists_card_eq
    have hdvd : Nat.card (P.map (QuotientGroup.mk' KC)) ∣ Nat.card (↥C ⧸ KC) :=
      Subgroup.card_subgroup_dvd_card _
    rw [hn] at hdvd
    have hn0 : n = 0 := by
      by_contra h0
      exact Nat.not_even_iff_odd.mpr (hoddIdx.of_dvd_nat hdvd) ((Nat.even_pow' h0).mpr even_two)
    rw [hn0, pow_zero] at hn
    have hbot := Subgroup.card_eq_one.mp hn
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  let q : ↥C →* (↥C ⧸ KC) := QuotientGroup.mk' KC
  let φ : ↥D →* (↥C ⧸ KC) := q.comp (Subgroup.inclusion hDC)
  have hφker : φ.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxK : ((x : ↥D) : G) ∈ K := by
      have h1 : (Subgroup.inclusion hDC x : ↥C) ∈ KC := by
        change (QuotientGroup.mk' KC) (Subgroup.inclusion hDC x) = 1 at hx
        exact (QuotientGroup.eq_one_iff _).mp hx
      simpa using Subgroup.mem_subgroupOf.mp h1
    have hxbot : ((x : ↥D) : G) ∈ K ⊓ D := ⟨hxK, x.2⟩
    rw [hKDbot] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hφker
  have hφsurj : Function.Surjective φ := by
    have hcardrange : Nat.card φ.range = Nat.card ↥D := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφinj]
      exact Subgroup.card_top
    have htop : φ.range = ⊤ :=
      Subgroup.eq_top_of_card_eq (H := φ.range) (by rw [hcardrange, hcardQuot])
    exact MonoidHom.range_eq_top.mp htop
  let e : ↥D ≃* (↥C ⧸ KC) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let g : F →* (↥C ⧸ KC) := q.comp F.subtype
  have hgrange : g.range = F.map q := by
    rw [show g = q.comp F.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  have hgker : g.ker = (F ⊓ KC).subgroupOf F := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change q (F.subtype x) = 1 ↔ (x : ↥C) ∈ F ∧ (x : ↥C) ∈ KC
    exact ⟨fun h => ⟨x.2, (QuotientGroup.eq_one_iff (F.subtype x)).mp h⟩,
      fun h => (QuotientGroup.eq_one_iff (F.subtype x)).mpr h.2⟩
  have hkercard : Nat.card g.ker = Nat.card ↥(F ⊓ KC) := by
    rw [hgker]
    have h := Subgroup.card_map_of_injective (Subgroup.subtype_injective F)
      (K := (F ⊓ KC).subgroupOf F)
    rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left : F ⊓ KC ≤ F)] at h
    exact h.symm
  have hQcard : Nat.card g.range ≤ 3 := by
    let Q : Subgroup ↥D := g.range.map e.symm.toMonoidHom
    let QG : Subgroup G := Q.map D.subtype
    have hQcard_eq : Nat.card Q = Nat.card g.range :=
      Subgroup.card_map_of_injective e.symm.injective (K := g.range)
    have hQGcard : Nat.card QG = Nat.card Q :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective D) (K := Q)
    have hQGle : QG ≤ Subgroup.centralizer (K : Set G) :=
      (Subgroup.map_subtype_le Q).trans hDK
    have hQgea : IsElemAbelian 3 g.range := by
      rw [hgrange]
      exact hFea.map q
    have hQGps : IsPGroup 3 QG :=
      ((hQgea.isPGroup.map e.symm.toMonoidHom).map D.subtype)
    have hQGea : IsElemAbelian 3 QG :=
      (hQgea.map e.symm.toMonoidHom).map D.subtype
    have : IsCyclic ↥QG := hA2 QG hQGle hQGps
    have h3 := CFSG.LocalAnalysis.GLTheoremA.KSubT.card_le_three_of_cyclic QG
      (fun x hx => hQGea.2 x hx)
    rwa [hQGcard, hQcard_eq] at h3
  have hFKCcard : Nat.card ↥(F ⊓ KC) ≤ 3 ^ 4 := by
    let A : Subgroup G := (F ⊓ KC).map C.subtype
    have hAea : IsElemAbelian 3 A := (hFea.mono inf_le_left).map C.subtype
    have hAleK : A ≤ K := by
      calc A = (F ⊓ KC).map C.subtype := rfl
        _ ≤ KC.map C.subtype := Subgroup.map_mono inf_le_right
        _ = K := Subgroup.map_subgroupOf_eq_of_le hKC'
    have hFGnorm : F.map C.subtype ≤
        Subgroup.normalizer ((P.map C.subtype : Subgroup G) : Set G) :=
      (Subgroup.map_mono hF).trans (Subgroup.le_normalizer_map (H := P) C.subtype)
    have hAnorm : A ≤ Subgroup.normalizer ((P.map C.subtype : Subgroup G) : Set G) :=
      (Subgroup.map_mono inf_le_left).trans hFGnorm
    have hPGleK : P.map C.subtype ≤ K := by
      calc P.map C.subtype ≤ KC.map C.subtype := Subgroup.map_mono hPle
        _ = K := Subgroup.map_subgroupOf_eq_of_le hKC'
    have hPGne : P.map C.subtype ≠ ⊥ := by
      intro hbot
      have hle : P ≤ C.subtype.ker :=
        (Subgroup.map_eq_bot_iff (H := P) (f := C.subtype)).mp hbot
      have hker : C.subtype.ker = ⊥ :=
        (MonoidHom.ker_eq_bot_iff C.subtype).mpr (Subgroup.subtype_injective C)
      rw [hker] at hle
      exact hPbot (le_bot_iff.mp hle)
    have hAcard : Nat.card A ≤ 3 ^ 4 :=
      hT5 G K hmark hKz (P.map C.subtype) A hPGleK hAleK hPGne
        (hP2.map C.subtype) hAea hAnorm
    have hAcard' : Nat.card A = Nat.card ↥(F ⊓ KC) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective C) (K := F ⊓ KC)
    rwa [hAcard'] at hAcard
  have hFcard : Nat.card F = Nat.card ↥(F ⊓ KC) * Nat.card g.range := by
    have h := Subgroup.card_ker_mul_card_range g
    rw [hkercard] at h
    exact h.symm
  calc Nat.card F = Nat.card ↥(F ⊓ KC) * Nat.card g.range := hFcard
    _ ≤ 3 ^ 4 * 3 := Nat.mul_le_mul hFKCcard hQcard
    _ = 3 ^ 5 := by norm_num

end CFSG.StandardType.FrameRoute.FS81

end
