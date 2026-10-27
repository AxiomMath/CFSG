module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

theorem exists_isCyclic_map_eq_of_isPGroup {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    [N.Normal] (hN : IsPGroup 2 N) {T : Subgroup (H ⧸ N)} (hT : IsCyclic T)
    (hodd : Odd (Nat.card T)) :
    ∃ Y : Subgroup H, IsCyclic Y ∧ Nat.card Y = Nat.card T ∧ Y.map (QuotientGroup.mk' N) = T := by
  classical
  haveI : IsCyclic ↥T := hT
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := ↥T)
  have htorder : orderOf t = Nat.card T := orderOf_eq_card_of_forall_mem_zpowers ht
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (t : H ⧸ N)
  have hxm : x ^ Nat.card T ∈ N := by
    rw [← QuotientGroup.eq_one_iff (x ^ Nat.card T)]
    change (QuotientGroup.mk' N) (x ^ Nat.card T) = 1
    rw [map_pow, hx]
    have h1 : (t : H ⧸ N) ^ orderOf (t : H ⧸ N) = 1 := pow_orderOf_eq_one _
    rwa [Subgroup.orderOf_coe, htorder] at h1
  obtain ⟨a, ha⟩ := hN ⟨x ^ Nat.card T, hxm⟩
  set n0 : ℕ := 2 ^ a with hn0
  have hxm_pow : (x ^ Nat.card T) ^ n0 = 1 := by
    have h1 := congrArg (Subtype.val) ha
    simpa [hn0] using h1
  have hcoppow : (orderOf (t : H ⧸ N)).Coprime n0 := by
    rw [Subgroup.orderOf_coe, htorder]
    simpa [hn0] using Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
  have hy_m : (x ^ n0) ^ Nat.card T = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact hxm_pow
  have hy_pi_order : orderOf (QuotientGroup.mk' N (x ^ n0)) = Nat.card T := by
    rw [map_pow, hx, Nat.Coprime.orderOf_pow hcoppow, Subgroup.orderOf_coe, htorder]
  have hordy : orderOf (x ^ n0) = Nat.card T :=
    Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.2 hy_m)
      (by rw [← hy_pi_order]; exact orderOf_map_dvd (QuotientGroup.mk' N) (x ^ n0))
  refine ⟨Subgroup.zpowers (x ^ n0), inferInstance, ?_, ?_⟩
  · rw [Nat.card_zpowers, hordy]
  · rw [MonoidHom.map_zpowers]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le,
        show QuotientGroup.mk' N (x ^ n0) = (t : H ⧸ N) ^ n0 from by rw [map_pow, hx]]
      exact T.pow_mem t.2 n0
    · rw [Nat.card_zpowers, hy_pi_order]

variable {G : Type} [Group G] [Finite G]
variable {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}

theorem s148_W148Quot_K_le_L (h : Hyp64 n M V₀ V g)
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G)) :
    K ≤ LOf V g := by
  rw [eq_sup_of_coe_eq_mul hKset]
  exact sup_le (fun u hu => Subgroup.mem_sup_left hu.1)
    (fun b hb => Subgroup.mem_sup_right hb.1)

theorem isPGroup_subgroupOf_LOf (h : Hyp64 n M V₀ V g)
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G)) :
    IsPGroup 2 ↥(K.subgroupOf (LOf V g)) := by
  have hKL : UOf M V g ⊔ BOf M V g ≤ LOf V g := by
    rw [← eq_sup_of_coe_eq_mul hKset]
    exact s148_W148Quot_K_le_L h hKset
  rw [eq_sup_of_coe_eq_mul hKset]
  exact (isPGroup_UOf_sup_BOf h).of_equiv (Subgroup.subgroupOfEquivOfLe hKL).symm

theorem mk_eq_one_iff_mem_UOf (h : Hyp64 n M V₀ V g) [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    {v : ↥(LOf V g)} (hv : (v : G) ∈ V) :
    QuotientGroup.mk' (K.subgroupOf (LOf V g)) v = 1 ↔ (v : G) ∈ UOf M V g := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff v, Subgroup.mem_subgroupOf,
    ← V_inf_K_eq_U h hKset]
  exact ⟨fun hvK => ⟨hv, hvK⟩, fun hvU => hvU.2⟩

theorem map_subgroupOf_conjSubgroup_eq [hK : (K.subgroupOf (LOf V g)).Normal] {l : G}
    (hlL : l ∈ LOf V g) (hlV : conjSubgroup V g = conjSubgroup V l) :
    ((conjSubgroup V g).subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))) =
      conjSubgroup ((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))))
        (QuotientGroup.mk' (K.subgroupOf (LOf V g)) ⟨l, hlL⟩) := by
  let L := LOf V g
  let π : ↥L →* (↥L ⧸ (K.subgroupOf L)) := QuotientGroup.mk' (K.subgroupOf L)
  change ((conjSubgroup V g).subgroupOf L).map π =
    conjSubgroup ((V.subgroupOf L).map π) (π ⟨l, hlL⟩)
  rw [hlV, map_conjSubgroup_of_hom, conjSubgroup_subgroupOf]

theorem mem_M_of_mk_mem_normalizer (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    {x : ↥(LOf V g)}
    (hx : QuotientGroup.mk' (K.subgroupOf (LOf V g)) x ∈
      normalizer (((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))) :
        Subgroup (↥(LOf V g) ⧸ K.subgroupOf (LOf V g))) :
          Set (↥(LOf V g) ⧸ K.subgroupOf (LOf V g)))) :
    (x : G) ∈ M := by
  let L := LOf V g
  let π : ↥L →* (↥L ⧸ (K.subgroupOf L)) := QuotientGroup.mk' (K.subgroupOf L)
  let A : Subgroup (↥L ⧸ (K.subgroupOf L)) := (V.subgroupOf L).map π
  have hx0 : π x ∈ Subgroup.normalizer (A : Set (↥L ⧸ (K.subgroupOf L))) := hx
  have hx' : x ∈ Subgroup.normalizer ((Subgroup.comap π A : Subgroup ↥L) : Set ↥L) :=
    Subgroup.le_normalizer_comap π hx0
  have hKL : K ≤ L := s148_W148Quot_K_le_L h hKset
  have hcomap : Subgroup.comap π A = (V ⊔ K).subgroupOf L := by
    rw [show A = (V.subgroupOf L).map π from rfl, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk']
    exact (Subgroup.subgroupOf_sup (le_sup_left : V ≤ L) hKL).symm
  rw [hcomap] at hx'
  have hsupL : V ⊔ K ≤ L := sup_le le_sup_left hKL
  have hxN : (x : G) ∈ Subgroup.normalizer ((V ⊔ K : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hy
    have hyL : y ∈ L := hsupL hy
    have hmem : x * (⟨y, hyL⟩ : ↥L) * x⁻¹ ∈ (V ⊔ K).subgroupOf L :=
      (Subgroup.mem_normalizer_iff.1 hx' (⟨y, hyL⟩ : ↥L)).1 hy
    change (x : G) * y * (x : G)⁻¹ ∈ V ⊔ K
    exact Subgroup.mem_subgroupOf.1 hmem
  rw [eq_sup_of_coe_eq_mul hKset] at hxN
  exact mem_M_of_mem_normalizer_sup h hgen x.2 hxN

theorem mem_conjM_of_mk_mem_normalizer (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    {x : ↥(LOf V g)}
    (hx : QuotientGroup.mk' (K.subgroupOf (LOf V g)) x ∈
      normalizer ((((conjSubgroup V g).subgroupOf (LOf V g)).map
        (QuotientGroup.mk' (K.subgroupOf (LOf V g))) :
          Subgroup (↥(LOf V g) ⧸ K.subgroupOf (LOf V g))) :
            Set (↥(LOf V g) ⧸ K.subgroupOf (LOf V g)))) :
    (x : G) ∈ conjSubgroup M g := by
  let L := LOf V g
  let π : ↥L →* (↥L ⧸ (K.subgroupOf L)) := QuotientGroup.mk' (K.subgroupOf L)
  let A : Subgroup (↥L ⧸ (K.subgroupOf L)) := ((conjSubgroup V g).subgroupOf L).map π
  have hx0 : π x ∈ Subgroup.normalizer (A : Set (↥L ⧸ (K.subgroupOf L))) := hx
  have hx' : x ∈ Subgroup.normalizer ((Subgroup.comap π A : Subgroup ↥L) : Set ↥L) :=
    Subgroup.le_normalizer_comap π hx0
  have hKL : K ≤ L := s148_W148Quot_K_le_L h hKset
  have hcomap : Subgroup.comap π A = (conjSubgroup V g ⊔ K).subgroupOf L := by
    rw [show A = ((conjSubgroup V g).subgroupOf L).map π from rfl, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk']
    exact (Subgroup.subgroupOf_sup (le_sup_right : conjSubgroup V g ≤ L) hKL).symm
  rw [hcomap] at hx'
  have hsupL : conjSubgroup V g ⊔ K ≤ L := sup_le le_sup_right hKL
  have hxN : (x : G) ∈
      Subgroup.normalizer ((conjSubgroup V g ⊔ K : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    intro y hy
    have hyL : y ∈ L := hsupL hy
    have hmem : x * (⟨y, hyL⟩ : ↥L) * x⁻¹ ∈ (conjSubgroup V g ⊔ K).subgroupOf L :=
      (Subgroup.mem_normalizer_iff.1 hx' (⟨y, hyL⟩ : ↥L)).1 hy
    change (x : G) * y * (x : G)⁻¹ ∈ conjSubgroup V g ⊔ K
    exact Subgroup.mem_subgroupOf.1 hmem
  rw [eq_sup_of_coe_eq_mul hKset] at hxN
  exact mem_conjM_of_mem_normalizer_sup h hgen x.2 hxN

theorem mem_NOf_of_mk_eq_mul (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    {l : G} (hlL : l ∈ LOf V g) (hlV : conjSubgroup V g = conjSubgroup V l) {x : ↥(LOf V g)}
    {c s₁ s₂ : ↥(LOf V g) ⧸ K.subgroupOf (LOf V g)}
    (hs₁ : s₁ ∈ conjSubgroup
      ((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) c)
    (hs₂ : s₂ ∈ conjSubgroup (conjSubgroup
      ((V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))))
        (QuotientGroup.mk' (K.subgroupOf (LOf V g)) ⟨l, hlL⟩)) c)
    (hs₁1 : s₁ ≠ 1) (hs₂1 : s₂ ≠ 1)
    (hx : QuotientGroup.mk' (K.subgroupOf (LOf V g)) x = s₁ * s₂) {k : G}
    (hk : k ∈ UOf M V g ⊔ BOf M V g) (hxk : (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ NOf M V g) :
    k ∈ NOf M V g := by
  obtain ⟨w, hwπ⟩ := QuotientGroup.mk'_surjective (K.subgroupOf (LOf V g)) c
  have hconjA : conjSubgroup ((V.subgroupOf (LOf V g)).map
        (QuotientGroup.mk' (K.subgroupOf (LOf V g))))
        (QuotientGroup.mk' (K.subgroupOf (LOf V g)) w) =
      ((conjSubgroup V (w : G)).subgroupOf (LOf V g)).map
        (QuotientGroup.mk' (K.subgroupOf (LOf V g))) := by
    rw [map_conjSubgroup_of_hom, conjSubgroup_subgroupOf]
  have hs₁'' : s₁ ∈ ((conjSubgroup V (w : G)).subgroupOf (LOf V g)).map
      (QuotientGroup.mk' (K.subgroupOf (LOf V g))) := by
    rw [← hwπ] at hs₁
    rwa [hconjA] at hs₁
  obtain ⟨t₁, ht₁, ht₁π⟩ := Subgroup.mem_map.1 hs₁''
  have hs₂'' : s₂ ∈ ((conjSubgroup (conjSubgroup V g) (w : G)).subgroupOf (LOf V g)).map
      (QuotientGroup.mk' (K.subgroupOf (LOf V g))) := by
    rw [← hwπ] at hs₂
    rw [← map_subgroupOf_conjSubgroup_eq hlL hlV] at hs₂
    rw [map_conjSubgroup_of_hom, conjSubgroup_subgroupOf] at hs₂
    exact hs₂
  obtain ⟨t₂, ht₂, ht₂π⟩ := Subgroup.mem_map.1 hs₂''
  have ht₁V : (w : G) * (t₁ : G) * (w : G)⁻¹ ∈ V :=
    (mem_conjSubgroup_iff).1 (Subgroup.mem_subgroupOf.1 ht₁)
  have ht₂Vg : (w : G) * (t₂ : G) * (w : G)⁻¹ ∈ conjSubgroup V g :=
    (mem_conjSubgroup_iff).1 (Subgroup.mem_subgroupOf.1 ht₂)
  set t₁' : G := (w : G) * (t₁ : G) * (w : G)⁻¹ with ht₁'def
  set t₂' : G := (w : G) * (t₂ : G) * (w : G)⁻¹ with ht₂'def
  set y' : G := (w : G) * (x : G) * (w : G)⁻¹ with hy'def
  set k' : G := (w : G) * k * (w : G)⁻¹ with hk'def
  have ht₁'V : t₁' ∈ V := by simpa [ht₁'def] using ht₁V
  have ht₂'Vg : t₂' ∈ conjSubgroup V g := by simpa [ht₂'def] using ht₂Vg
  have ht₁'U : t₁' ∉ UOf M V g := by
    intro hU
    have ht₁K : (t₁ : G) ∈ UOf M V g ⊔ BOf M V g := by
      have h₁ := s148_W148Basic_conj_mem_sup h ((LOf V g).inv_mem w.2)
        (Subgroup.mem_sup_left (by simpa [ht₁'def] using hU))
      convert h₁ using 1
      group
    have hπ1 : QuotientGroup.mk' (K.subgroupOf (LOf V g)) t₁ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff t₁, Subgroup.mem_subgroupOf,
        eq_sup_of_coe_eq_mul hKset]
      exact ht₁K
    rw [ht₁π] at hπ1
    exact hs₁1 hπ1
  have ht₂'B : t₂' ∉ BOf M V g := by
    intro hB
    have ht₂K : (t₂ : G) ∈ UOf M V g ⊔ BOf M V g := by
      have h₁ := s148_W148Basic_conj_mem_sup h ((LOf V g).inv_mem w.2)
        (Subgroup.mem_sup_right (by simpa [ht₂'def] using hB))
      convert h₁ using 1
      group
    have hπ2 : QuotientGroup.mk' (K.subgroupOf (LOf V g)) t₂ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff t₂, Subgroup.mem_subgroupOf,
        eq_sup_of_coe_eq_mul hKset]
      exact ht₂K
    rw [ht₂π] at hπ2
    exact hs₂1 hπ2
  have hπ12 : QuotientGroup.mk' (K.subgroupOf (LOf V g)) ((t₁ * t₂)⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, map_mul, ht₁π, ht₂π, hx]
    group
  have hmemL : (t₁ * t₂)⁻¹ * x ∈ K.subgroupOf (LOf V g) := by
    rw [← QuotientGroup.eq_one_iff ((t₁ * t₂)⁻¹ * x)]
    exact hπ12
  have hmemK : ((t₁ : G) * (t₂ : G))⁻¹ * (x : G) ∈ K := by
    simpa using Subgroup.mem_subgroupOf.1 hmemL
  have hconj12 : (t₁' * t₂')⁻¹ * y' ∈ UOf M V g ⊔ BOf M V g := by
    have hK12 : ((t₁ : G) * (t₂ : G))⁻¹ * (x : G) ∈ UOf M V g ⊔ BOf M V g := by
      rw [← eq_sup_of_coe_eq_mul hKset]; exact hmemK
    have h₁ := s148_W148Basic_conj_mem_sup h w.2 hK12
    convert h₁ using 1
    rw [ht₁'def, ht₂'def, hy'def]
    group
  have hk'K : k' ∈ UOf M V g ⊔ BOf M V g :=
    s148_W148Basic_conj_mem_sup h w.2 hk
  have hE : y' * k' * y'⁻¹ * k'⁻¹ ∈ NOf M V g := by
    have h₁ : (w : G) * ((x : G) * k * (x : G)⁻¹ * k⁻¹) * (w : G)⁻¹ ∈ NOf M V g := by
      have hmem : (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ conjSubgroup (NOf M V g) (w : G) := by
        rw [conjSubgroup_NOf_eq h w.2]; exact hxk
      exact (mem_conjSubgroup_iff).1 hmem
    convert h₁ using 1
    rw [hy'def, hk'def]
    group
  have hk' : k' ∈ NOf M V g :=
    mem_NOf_of_conj_mul_inv_mem h hgen ht₁'V ht₁'U ht₂'Vg ht₂'B hconj12 hk'K hE
  have hkconj : k ∈ conjSubgroup (NOf M V g) (w : G) := by
    rw [mem_conjSubgroup_iff]
    exact hk'
  rwa [conjSubgroup_NOf_eq h w.2] at hkconj

end CFSG.LocalAnalysis.WeakClosure81
