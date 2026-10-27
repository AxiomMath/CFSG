module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3M0
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A4

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup
open CFSG.LocalAnalysis.GLTheoremA.CatB

section M1
variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem M1_K (h : FF84Sec3 b L B b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    ∃ K : Subgroup G, K ≤ L ⊓ Cen (b₁ * b₂) ∧ Nat.card K = 60 ∧ IsSimpleGroup K ∧
      b₁ * b₂ ^ 2 ∈ K ∧ b₁ * b₂ ∉ K ∧ Subgroup.zpowers (b₁ * b₂) ⊔ K = L ⊓ Cen (b₁ * b₂) ∧
      ∀ g ∈ Cen b ⊓ Cen (b₁ * b₂), conjBy g K = K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, he⟩ := M0_model h hZ
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  obtain ⟨y₁, hy₁⟩ : ∃ y : ↥L, (y : G) = b₁ := ⟨⟨b₁, hb₁L⟩, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y : ↥L, (y : G) = b₂ := ⟨⟨b₂, hb₂L⟩, rfl⟩
  obtain ⟨hm₁, hm₂⟩ := he y₁ y₂ hy₁ hy₂
  obtain ⟨yc, hyc⟩ : ∃ y : ↥L, (y : G) = b₁ * b₂ := ⟨y₁ * y₂, by simp [hy₁, hy₂]⟩
  have hycy : yc = y₁ * y₂ := Subtype.ext (by simp [hy₁, hy₂, hyc])
  have hc : ((e yc : alternatingGroup (Fin 8)) : P8) = m₁ * m₂ := by
    rw [hycy, map_mul, Subgroup.coe_mul, hm₁, hm₂]
  have hcL : b₁ * b₂ ∈ L := by rw [← hyc]; exact yc.2
  have hcomm_iff : ∀ a : ↥L, ((e a : alternatingGroup (Fin 8)) : P8) * (m₁ * m₂) =
      (m₁ * m₂) * ((e a : alternatingGroup (Fin 8)) : P8) ↔
      (a : G) * (b₁ * b₂) = (b₁ * b₂) * (a : G) := by
    intro a
    have h1 : ((e (a * yc) : alternatingGroup (Fin 8)) : P8) =
        ((e a : alternatingGroup (Fin 8)) : P8) * (m₁ * m₂) := by
      rw [map_mul, Subgroup.coe_mul, hc]
    have h2 : ((e (yc * a) : alternatingGroup (Fin 8)) : P8) =
        (m₁ * m₂) * ((e a : alternatingGroup (Fin 8)) : P8) := by
      rw [map_mul, Subgroup.coe_mul, hc]
    constructor
    · intro hcm
      have hay : a * yc = yc * a := e.injective (Subtype.ext (by rw [h1, h2]; exact hcm))
      rw [← hyc]
      exact congrArg Subtype.val hay
    · intro hcm
      have hay : a * yc = yc * a :=
        Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hyc]; exact hcm)
      rw [← h1, ← h2]
      exact congrArg Subtype.val (congrArg e hay)
  have hK5sup : Subgroup.zpowers (m₁ * m₂) ⊔ K5 =
      Subgroup.centralizer ({m₁ * m₂} : Set P8) ⊓ A8s := by
    rw [← centralizer_c_eq_map, a8_centralizer, Subgroup.map_sup, MonoidHom.map_zpowers]
    have hc8 : (alternatingGroup (Fin 8)).subtype a8c8 = (m₁ * m₂)⁻¹ := a8c8_val_eq_inv
    rw [hc8, Subgroup.zpowers_inv, sup_comm]
  have hcn : ∀ x : P8, x * (m₁ * m₂) = (m₁ * m₂) * x →
      x ∈ Subgroup.normalizer (K5 : Set P8) := by
    intro x hx
    have hxC : Commute x (m₁ * m₂) := hx
    have hx' : x⁻¹ * (m₁ * m₂) = (m₁ * m₂) * x⁻¹ := (Commute.inv_left_iff.2 hxC).eq
    refine Subgroup.mem_normalizer_iff.2 (fun n => ⟨fun hn => K5_normal_cent x hx n hn, fun hn => ?_⟩)
    have key := K5_normal_cent x⁻¹ hx' _ hn
    have e1 : x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n := by group
    rwa [e1] at key
  have hLE : Subgroup.zpowers (m₁ * m₂) ≤ Subgroup.normalizer (K5 : Set P8) :=
    Subgroup.zpowers_le.2 (hcn _ rfl)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers (m₁ * m₂)) K5 hLE
  have hdecomp : ∀ a : P8, a ∈ Subgroup.centralizer ({m₁ * m₂} : Set P8) ⊓ A8s →
      ∃ j : ℤ, ∃ k ∈ K5, (m₁ * m₂) ^ j * k = a := by
    intro a ha
    have ha' : a ∈ (↑(Subgroup.zpowers (m₁ * m₂) ⊔ K5) : Set P8) := by
      rw [SetLike.mem_coe, hK5sup]
      exact ha
    rw [hset] at ha'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 ha'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (SetLike.mem_coe.1 hx)
    exact ⟨j, y, SetLike.mem_coe.1 hy, hxy⟩
  set ψ : ↥L →* P8 := (alternatingGroup (Fin 8)).subtype.comp e.toMonoidHom with hψdef
  have hψ : ∀ x : ↥L, ψ x = ((e x : alternatingGroup (Fin 8)) : P8) := fun x => rfl
  have hψi : Function.Injective ψ := fun a b hab =>
    e.injective (Subtype.ext ((hψ a).symm.trans (hab.trans (hψ b))))
  set K0 : Subgroup ↥L := K5.comap ψ with hK0def
  set K : Subgroup G := K0.map L.subtype with hKdef
  have hmemK0 : ∀ x : ↥L, x ∈ K0 ↔ ((e x : alternatingGroup (Fin 8)) : P8) ∈ K5 :=
    fun x => Subgroup.mem_comap
  have hψyc : ψ yc = m₁ * m₂ := hc
  have hcK5 : (m₁ * m₂) ∉ K5 := by
    rintro ⟨x, hx, hxeq⟩
    have h0 : ((x : A8) : P8) 0 = 0 := ((mem_a8Kb_iff x).1 hx).1
    have hxe : ((x : A8) : P8) = m₁ * m₂ := hxeq
    rw [hxe] at h0
    exact absurd h0 (by decide)
  have hdK5 : m₁ * m₂ ^ 2 ∈ K5 := by
    have e_d : m₁ * m₂ ^ 2 = (List.formPerm [3, 5, 4] : P8) := by decide +kernel
    have hx0K : (⟨List.formPerm [3, 5, 4], formPerm_354_mem⟩ : A8) ∈ a8Kb :=
      (mem_a8Kb_iff _).2 ⟨by decide, by decide, by decide⟩
    rw [e_d]
    exact Subgroup.mem_map.2 ⟨⟨List.formPerm [3, 5, 4], formPerm_354_mem⟩, hx0K, rfl⟩
  have hyd : ((e (y₁ * y₂ ^ 2) : alternatingGroup (Fin 8)) : P8) = m₁ * m₂ ^ 2 := by
    rw [map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, hm₁, hm₂]
  have hbd : b₁ * b₂ ^ 2 ∈ K := by
    refine Subgroup.mem_map.2 ⟨y₁ * y₂ ^ 2, (hmemK0 _).2 (by rw [hyd]; exact hdK5), ?_⟩
    simp [hy₁, hy₂]
  have hcK : b₁ * b₂ ∉ K := by
    intro hmem
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.1 hmem
    have hkc : k = yc := Subtype.ext (by rw [hyc]; exact hkeq)
    rw [hkc, hmemK0, hc] at hk
    exact hcK5 hk
  have hKle : K ≤ L ⊓ Cen (b₁ * b₂) := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hz
    have hk5 : ((e k : alternatingGroup (Fin 8)) : P8) ∈ K5 := (hmemK0 k).1 hk
    have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (K5_le_cent hk5)
    exact Subgroup.mem_inf.2 ⟨k.2, Subgroup.mem_centralizer_singleton_iff.2 ((hcomm_iff k).1 hcomm)⟩
  have hsup : Subgroup.zpowers (b₁ * b₂) ⊔ K = L ⊓ Cen (b₁ * b₂) := by
    apply le_antisymm
    · exact sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2
        ⟨hcL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩)) hKle
    · intro g hg
      obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨gL, hgLg⟩ : ∃ x : ↥L, (x : G) = g := ⟨⟨g, hgL⟩, rfl⟩
      have hgcomm : ((e gL : alternatingGroup (Fin 8)) : P8) * (m₁ * m₂) =
          (m₁ * m₂) * ((e gL : alternatingGroup (Fin 8)) : P8) :=
        (hcomm_iff gL).2 (by rw [hgLg]; exact Subgroup.mem_centralizer_singleton_iff.1 hgC)
      have haC : ((e gL : alternatingGroup (Fin 8)) : P8) ∈
          Subgroup.centralizer ({m₁ * m₂} : Set P8) ⊓ A8s :=
        Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hgcomm, (e gL).2⟩
      obtain ⟨j, k', hk', hjk⟩ := hdecomp _ haC
      obtain ⟨w, hw⟩ : ∃ w : ↥L, ((e w : alternatingGroup (Fin 8)) : P8) = k' :=
        ⟨e.symm ⟨k', K5_le_A8 hk'⟩, by rw [MulEquiv.apply_symm_apply]⟩
      have hwK0 : w ∈ K0 := (hmemK0 w).2 (by rw [hw]; exact hk')
      have hgeq : gL = yc ^ j * w := by
        apply hψi
        rw [map_mul, map_zpow, hψyc, hψ w, hw, hjk, hψ gL]
      have hgg : g = (b₁ * b₂) ^ j * (w : G) := by
        rw [← hgLg, hgeq]
        simp [hyc]
      rw [hgg]
      exact mul_mem (Subgroup.mem_sup_left (zpow_mem (Subgroup.mem_zpowers _) j))
        (Subgroup.mem_sup_right (Subgroup.mem_map.2 ⟨w, hwK0, rfl⟩))
  have hψrange : K5 ≤ ψ.range := by
    intro z hz
    refine MonoidHom.mem_range.2 ⟨e.symm ⟨z, K5_le_A8 hz⟩, ?_⟩
    rw [hψ, MulEquiv.apply_symm_apply]
  have hmapK0 : K0.map ψ = K5 :=
    (Subgroup.map_comap_eq ψ K5).trans (inf_eq_right.2 hψrange)
  have hcK0 : Nat.card K0 = 60 := by
    have h1 : Nat.card (K0.map ψ) = Nat.card K0 := Subgroup.card_map_of_injective hψi
    rw [hmapK0, K5_card] at h1
    exact h1.symm
  have hKcard : Nat.card K = 60 := by
    have h1 : Nat.card (K0.map L.subtype) = Nat.card K0 :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    exact h1.trans hcK0
  have hKsimple : IsSimpleGroup K := by
    haveI := K5_simple
    let eK : ↥K ≃* ↥K5 :=
      ((Subgroup.equivMapOfInjective K0 L.subtype (Subgroup.subtype_injective _)).symm.trans
        (Subgroup.equivMapOfInjective K0 ψ hψi)).trans (MulEquiv.subgroupCongr hmapK0)
    exact MulEquiv.isSimpleGroup eK
  have hL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp h.hyp.quasi.1
  obtain ⟨e', he'⟩ : ∃ e' : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8),
      ∀ x : ↥L, e' (QuotientGroup.mk x) = e x :=
    ⟨(M0_quotIso hZ).trans e, fun x => by simp [M0_quotIso_mk]⟩
  obtain ⟨θ, hθc, -, -⟩ := M0_T0_conj hL e'
  have hKey : ∀ g ∈ Cen b ⊓ Cen (b₁ * b₂), ∀ z ∈ K, g * z * g⁻¹ ∈ K := by
    intro g hg z hz
    obtain ⟨hgb, hgc⟩ := Subgroup.mem_inf.1 hg
    have hgN : g ∈ Nor L := h.hyp.hLN hgb
    have hgc' : g * (b₁ * b₂) = (b₁ * b₂) * g := Subgroup.mem_centralizer_singleton_iff.1 hgc
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hz
    show g * (k : G) * g⁻¹ ∈ K
    have hgk : g * (k : G) * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hgN k).1 k.2
    obtain ⟨x, hx⟩ : ∃ x : ↥L, (x : G) = g * (k : G) * g⁻¹ := ⟨⟨_, hgk⟩, rfl⟩
    have hτc : θ ⟨g, hgN⟩ * (m₁ * m₂) = (m₁ * m₂) * θ ⟨g, hgN⟩ := by
      have h1 := hθc g hgN yc yc (by rw [hyc, hgc']; group)
      rw [he' yc, hc] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1.symm
    have hxE : ((e x : alternatingGroup (Fin 8)) : P8) =
        θ ⟨g, hgN⟩ * ((e k : alternatingGroup (Fin 8)) : P8) * (θ ⟨g, hgN⟩)⁻¹ := by
      rw [← he' x, ← he' k]
      exact hθc g hgN k x hx
    have hk5 : ((e k : alternatingGroup (Fin 8)) : P8) ∈ K5 := (hmemK0 k).1 hk
    have hxK5 : ((e x : alternatingGroup (Fin 8)) : P8) ∈ K5 := by
      rw [hxE]
      exact K5_normal_cent _ hτc _ hk5
    have hxK0 : x ∈ K0 := (hmemK0 x).2 hxK5
    rw [← hx]
    exact Subgroup.mem_map.2 ⟨x, hxK0, rfl⟩
  refine ⟨K, hKle, hKcard, hKsimple, hbd, hcK, hsup, ?_⟩
  intro g hg
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    show g * z * g⁻¹ ∈ K
    exact hKey g hg z hz
  · intro z hz
    have hy := hKey g⁻¹ (Subgroup.inv_mem _ hg) z hz
    rw [inv_inv] at hy
    exact Subgroup.mem_map.2 ⟨g⁻¹ * z * g, hy, by show g * (g⁻¹ * z * g) * g⁻¹ = z; group⟩

end M1

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
