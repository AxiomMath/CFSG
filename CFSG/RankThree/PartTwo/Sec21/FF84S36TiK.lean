module

public import CFSG.RankThree.PartTwo.Sec21.FF84S36TiT
public import CFSG.RankThree.PartTwo.Sec21.FF84S36TiHyp
public import CFSG.RankThree.PartTwo.Sec21.FF84S36Ab
public import CFSG.RankThree.PartTwo.Sec21.FF84S36Gen

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG.Quasithin
open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb)

variable {G : Type} [Group G] [Finite G]

theorem S36_isPGroup_map {H K : Type} [Group H] [Group K] (f : H →* K) {P : Subgroup H}
    (hP : IsPGroup 2 P) : IsPGroup 2 (P.map f) := by
  intro g
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h2 : (g : K) = f x := hxg.symm
  rw [Subgroup.coe_pow, Subgroup.coe_one, h2, ← map_pow, h1, map_one]

theorem S36_isPGroup_comap {H K : Type} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) {P : Subgroup K} (hP : IsPGroup 2 P) :
    IsPGroup 2 (P.comap f) := by
  intro g
  obtain ⟨k, hk⟩ := hP ⟨f (g : H), g.2⟩
  refine ⟨k, Subtype.ext (hf ?_)⟩
  have h1 : (f (g : H)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
  exact h1

theorem S36_map_cen (c : G ≃* G) (x : G) : (Cen x).map c.toMonoidHom = Cen (c x) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    apply S36_mem_cen_of
    show c x * c w = c w * c x
    rw [← map_mul, ← map_mul, S36_comm_of_cen hw]
  · intro hy
    refine ⟨c.symm y, S36_mem_cen_of ?_, by simp⟩
    apply c.injective
    rw [map_mul, map_mul, c.apply_symm_apply]
    exact S36_comm_of_cen hy

def S36_emb {L : Subgroup G} (e : ↥L ≃* alternatingGroup (Fin 8)) : ↥L →* P8 :=
  (alternatingGroup (Fin 8)).subtype.comp e.toMonoidHom

theorem S36_A9_transport (hA9 : A9CentralizerStmt) {L : Subgroup G}
    (e : ↥L ≃* alternatingGroup (Fin 8)) {bk bj s : G} (hbk : bk ∈ L) (hbj : bj ∈ L)
    (hsL : s ∈ L) (hek : ((e ⟨bk, hbk⟩ : alternatingGroup (Fin 8)) : P8) = m₁)
    (hej : ((e ⟨bj, hbj⟩ : alternatingGroup (Fin 8)) : P8) = m₂)
    (hs2 : s * s = 1) (hsk : s * bk * s⁻¹ = bk⁻¹) (hsj : s * bj * s⁻¹ = bj) :
    ∃ Q : Subgroup G, Q ≤ Cen s ⊓ L ∧ (Q.subgroupOf (Cen s ⊓ L)).Normal ∧ IsPGroup 2 Q ∧
      ExtraspecialAt Q s ∧ (∃ A : Subgroup G, A ≤ Q ∧ IsElemAb 2 3 A) ∧
      ∀ R : Subgroup G, R ≤ Cen s ⊓ L → IsPGroup 2 R →
        (R.subgroupOf (Cen s ⊓ L)).Normal → R ≤ Q := by
  classical
  let φ : ↥L →* P8 := S36_emb e
  have hφinj : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hφA : ∀ y : ↥L, φ y ∈ A8s := fun y => (e y).2
  have hφrange : ∀ g ∈ A8s, ∃ y : ↥L, φ y = g := fun g hg =>
    ⟨e.symm ⟨g, hg⟩, by simp [φ, S36_emb]⟩
  have hφbk : φ ⟨bk, hbk⟩ = m₁ := hek
  have hφbj : φ ⟨bj, hbj⟩ = m₂ := hej
  have hzz : (⟨s, hsL⟩ : ↥L) * ⟨s, hsL⟩ = 1 := Subtype.ext (by simpa using hs2)
  have hzk : (⟨s, hsL⟩ : ↥L) * ⟨bk, hbk⟩ * (⟨s, hsL⟩ : ↥L)⁻¹ = (⟨bk, hbk⟩ : ↥L)⁻¹ :=
    Subtype.ext (by simpa using hsk)
  have hzj : (⟨s, hsL⟩ : ↥L) * ⟨bj, hbj⟩ * (⟨s, hsL⟩ : ↥L)⁻¹ = ⟨bj, hbj⟩ :=
    Subtype.ext (by simpa using hsj)
  have hs₀A : φ ⟨s, hsL⟩ ∈ A8s := hφA _
  have hs₀2 : φ ⟨s, hsL⟩ * φ ⟨s, hsL⟩ = 1 := by rw [← map_mul, hzz, map_one]
  have hs₀m1 : φ ⟨s, hsL⟩ * m₁ * (φ ⟨s, hsL⟩)⁻¹ = m₁⁻¹ := by
    have key : φ ⟨s, hsL⟩ * φ ⟨bk, hbk⟩ * (φ ⟨s, hsL⟩)⁻¹ =
        φ (⟨s, hsL⟩ * ⟨bk, hbk⟩ * (⟨s, hsL⟩ : ↥L)⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hzk, map_inv, hφbk] at key
    exact key
  have hs₀m2 : φ ⟨s, hsL⟩ * m₂ * (φ ⟨s, hsL⟩)⁻¹ = m₂ := by
    have key : φ ⟨s, hsL⟩ * φ ⟨bj, hbj⟩ * (φ ⟨s, hsL⟩)⁻¹ =
        φ (⟨s, hsL⟩ * ⟨bj, hbj⟩ * (⟨s, hsL⟩ : ↥L)⁻¹) := by
      simp only [map_mul, map_inv]
    rw [hzj, hφbj] at key
    exact key
  have hs₁ : φ ⟨s, hsL⟩ ≠ 1 := by
    intro h1
    simp only [h1, one_mul, inv_one, mul_one] at hs₀m1
    have hmm : m₁ * m₁ ≠ 1 := by decide
    exact hmm (mul_eq_one_iff_eq_inv.2 hs₀m1)
  obtain ⟨-, Q', hQA, hQC, hQN, hQp, hQcard, hsQ, hQcen, hQext, ⟨A', hA'Q', hA'el⟩, hmax⟩ :=
    hA9 (φ ⟨s, hsL⟩) hs₀A hs₀2 hs₀m1 hs₀m2
  have hQLmap : (Q'.comap φ).map φ = Q' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hx⟩ := hφrange y (hQA hy)
      exact ⟨x, Subgroup.mem_comap.2 (by rw [hx]; exact hy), hx⟩
  have hmapcomap : ∀ Y : Subgroup P8, Y ≤ A8s → (Y.comap φ).map φ = Y := by
    intro Y hY
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, hx⟩ := hφrange y (hY hy)
      exact ⟨x, Subgroup.mem_comap.2 (by rw [hx]; exact hy), hx⟩
  have hAL : IsElemAb 2 3 (A'.comap φ) :=
    S36_elemAb_of_map φ hφinj (by rw [hmapcomap A' (hA'Q'.trans hQA)]; exact hA'el)
  have hQLext : ExtraspecialAt (Q'.comap φ) ⟨s, hsL⟩ := by
    apply S36_ext_refl φ hφinj
    rw [hQLmap]
    exact S36_ext_of_isExtraspecial hQext hQcard hsQ hs₀2 hs₁ hQcen
  refine ⟨(Q'.comap φ).map L.subtype, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro x ⟨w, hw, rfl⟩
    have hwC : (⟨s, hsL⟩ : ↥L) * w = w * ⟨s, hsL⟩ := by
      apply hφinj
      rw [map_mul, map_mul]
      exact S36_comm_of_cen (hQC (Subgroup.mem_comap.1 hw))
    refine Subgroup.mem_inf.2 ⟨S36_mem_cen_of ?_, w.2⟩
    simpa using congrArg Subtype.val hwC
  ·
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨w, hw, hwn⟩ := Subgroup.mem_map.1 hn
    have hwn' : (w : G) = (n : G) := hwn
    obtain ⟨hgC, hgL⟩ := Subgroup.mem_inf.1 g.2
    have hzy : (⟨s, hsL⟩ : ↥L) * ⟨(g : G), hgL⟩ = ⟨(g : G), hgL⟩ * ⟨s, hsL⟩ :=
      Subtype.ext (S36_comm_of_cen hgC)
    have hyC : φ ⟨(g : G), hgL⟩ ∈ Cen (φ ⟨s, hsL⟩) :=
      S36_mem_cen_of (by rw [← map_mul, ← map_mul, hzy])
    have hwQ : φ w ∈ Q' := Subgroup.mem_comap.1 hw
    have hwK : φ w ∈ Cen (φ ⟨s, hsL⟩) ⊓ A8s := ⟨hQC hwQ, hQA hwQ⟩
    have hyK : φ ⟨(g : G), hgL⟩ ∈ Cen (φ ⟨s, hsL⟩) ⊓ A8s := ⟨hyC, hφA _⟩
    have hconj := Subgroup.Normal.conj_mem hQN ⟨φ w, hwK⟩
      (Subgroup.mem_subgroupOf.2 hwQ) ⟨φ ⟨(g : G), hgL⟩, hyK⟩
    have hconjQ : φ ⟨(g : G), hgL⟩ * φ w * (φ ⟨(g : G), hgL⟩)⁻¹ ∈ Q' :=
      Subgroup.mem_subgroupOf.1 hconj
    refine Subgroup.mem_map.2 ⟨⟨(g : G), hgL⟩ * w * ⟨(g : G), hgL⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact hconjQ
    · simp [hwn']
  · exact S36_isPGroup_map L.subtype (S36_isPGroup_comap φ hφinj hQp)
  · exact S36_ext_fwd L.subtype Subtype.val_injective hQLext
  · exact ⟨(A'.comap φ).map L.subtype, Subgroup.map_mono (Subgroup.comap_mono hA'Q'),
      S36_elemAb_map L.subtype Subtype.val_injective hAL⟩
  ·
    intro R hRK hRp hRN
    have hR'sub : (R.comap L.subtype).map φ ≤ Cen (φ ⟨s, hsL⟩) ⊓ A8s := by
      rintro _ ⟨x, hx, rfl⟩
      have hxK := hRK (Subgroup.mem_comap.1 hx)
      have hzx : (⟨s, hsL⟩ : ↥L) * x = x * ⟨s, hsL⟩ :=
        Subtype.ext (S36_comm_of_cen (Subgroup.mem_inf.1 hxK).1)
      exact ⟨S36_mem_cen_of (by rw [← map_mul, ← map_mul, hzx]), hφA x⟩
    have hR'p : IsPGroup 2 ((R.comap L.subtype).map φ) :=
      S36_isPGroup_map φ (S36_isPGroup_comap L.subtype Subtype.val_injective hRp)
    have hR'N : (((R.comap L.subtype).map φ).subgroupOf (Cen (φ ⟨s, hsL⟩) ⊓ A8s)).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨x, hx, hxn⟩ := Subgroup.mem_map.1 hn
      obtain ⟨hgC, hgA⟩ := Subgroup.mem_inf.1 g.2
      obtain ⟨y, hy⟩ := hφrange (g : P8) hgA
      have hzy : (⟨s, hsL⟩ : ↥L) * y = y * ⟨s, hsL⟩ := by
        apply hφinj
        rw [map_mul, map_mul, hy]
        exact S36_comm_of_cen hgC
      have hyC : (y : G) ∈ Cen s := S36_mem_cen_of (by simpa using congrArg Subtype.val hzy)
      have hxR : (x : G) ∈ R := Subgroup.mem_comap.1 hx
      have hxK : (x : G) ∈ Cen s ⊓ L := hRK hxR
      have hconj := Subgroup.Normal.conj_mem hRN ⟨(x : G), hxK⟩
        (Subgroup.mem_subgroupOf.2 hxR) ⟨(y : G), Subgroup.mem_inf.2 ⟨hyC, y.2⟩⟩
      have hconjR : (y : G) * (x : G) * (y : G)⁻¹ ∈ R := Subgroup.mem_subgroupOf.1 hconj
      refine Subgroup.mem_map.2 ⟨y * x * y⁻¹, Subgroup.mem_comap.2 ?_, ?_⟩
      · simpa using hconjR
      · simp [hy, hxn]
    have hR'Q : (R.comap L.subtype).map φ ≤ Q' :=
      hmax _ hR'sub hR'p hR'N
    intro x hx
    have hxL : x ∈ L := (Subgroup.mem_inf.1 (hRK hx)).2
    have hwQ : φ ⟨x, hxL⟩ ∈ Q' := hR'Q (Subgroup.mem_map.2 ⟨⟨x, hxL⟩, Subgroup.mem_comap.2 hx, rfl⟩)
    exact Subgroup.mem_map.2 ⟨⟨x, hxL⟩, hwQ, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
