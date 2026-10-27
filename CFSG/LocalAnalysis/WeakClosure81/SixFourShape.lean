module

public import CFSG.LocalAnalysis.WeakClosure81.SixFour

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_sr_eq_of_mul_self_eq_one {m : ℕ} (hm : Odd m) {z : DihedralGroup m}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) : ∃ i, z = DihedralGroup.sr i := by
  cases z with
  | r j =>
    exfalso
    apply hz1
    have h2j : j + j = 0 := by
      have hh : DihedralGroup.r (j + j) = DihedralGroup.r 0 := by
        rw [DihedralGroup.r_mul_r] at hz2
        exact hz2
      exact DihedralGroup.r.inj hh
    rw [(ZMod.add_self_eq_zero_iff_eq_zero hm).1 h2j]
    exact DihedralGroup.r_zero
  | sr j => exact ⟨j, rfl⟩

theorem nat_card_le_two_of_isElemAbelian_dihedral {m : ℕ} (hm : Odd m)
    {E : Subgroup (DihedralGroup m)} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 2 := by
  haveI : NeZero m := ⟨hm.pos.ne'⟩
  by_cases hbot : E = ⊥
  · rw [hbot, Subgroup.card_bot]; norm_num
  · obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
    have hxmem : (x : DihedralGroup m) ∈ E := x.2
    have hx2 : (x : DihedralGroup m) * x = 1 := IsElemAbelian.mul_self_eq_one hE hxmem
    obtain ⟨i, hxi⟩ := exists_sr_eq_of_mul_self_eq_one hm hx2 (fun h => hx1 (Subtype.ext h))
    have hle : E ≤ Subgroup.zpowers (DihedralGroup.sr i) := by
      intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]; exact Subgroup.one_mem _
      · have hy2 : y * y = 1 := IsElemAbelian.mul_self_eq_one hE hy
        obtain ⟨j, hyj⟩ := exists_sr_eq_of_mul_self_eq_one hm hy2 hy1
        have hcomm : DihedralGroup.sr i * DihedralGroup.sr j
            = DihedralGroup.sr j * DihedralGroup.sr i := by
          rw [← hxi, ← hyj]
          exact IsElemAbelian.comm hE hxmem hy
        have hji : j - i = i - j := by
          have hh : DihedralGroup.r (j - i) = DihedralGroup.r (i - j) := by
            simpa using hcomm
          exact DihedralGroup.r.inj hh
        have h2 : j + j = i + i := by
          have := congrArg (fun t : ZMod m => t + (i + j)) hji
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
        have hzero : j - i = 0 := by
          have hsum : (j - i) + (j - i) = 0 := by
            have hsub : (j - i) + (j - i) = (j + j) - (i + i) := by ring
            rw [hsub, h2, sub_self]
          exact (ZMod.add_self_eq_zero_iff_eq_zero hm).1 hsum
        have hji' : j = i := sub_eq_zero.1 hzero
        rw [hyj, hji']
        exact Subgroup.mem_zpowers _
    have hxne : (DihedralGroup.sr i : DihedralGroup m) ≠ 1 := by
      intro h
      exact hx1 (Subtype.ext (by simp [hxi, h]))
    have hord : orderOf (DihedralGroup.sr i) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact DihedralGroup.sr_mul_self i) hxne
    calc Nat.card E ≤ Nat.card (Subgroup.zpowers (DihedralGroup.sr i)) :=
          Subgroup.card_le_of_le hle
      _ = orderOf (DihedralGroup.sr i) := Nat.card_zpowers (DihedralGroup.sr i)
      _ = 2 := hord

theorem mem_U_of_commutator_le_N_of_ne {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) (hUV : UOf M V g ≠ V)
    {k : G} (hkK : k ∈ UOf M V g ⊔ BOf M V g)
    (hkV : ∀ v ∈ V, ⁅k, v⁆ ∈ NOf M V g) : k ∈ UOf M V g := by
  obtain ⟨v₀, hv₀V, hv₀U⟩ : ∃ v ∈ V, v ∉ UOf M V g := by
    by_contra hcon
    push Not at hcon
    exact hUV (le_antisymm inf_le_left hcon)
  exact stepB h hgen hv₀V hv₀U k hkK (hkV v₀ hv₀V)

theorem conjSubgroup_U_eq_of_sup_eq_of_ne {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) (hUV : UOf M V g ≠ V)
    {x : G} (hxL : x ∈ LOf V g)
    (hxK : conjSubgroup V x ⊔ (UOf M V g ⊔ BOf M V g)
      = V ⊔ (UOf M V g ⊔ BOf M V g)) :
    conjSubgroup (UOf M V g) x = UOf M V g := by
  have hcopy := h
  obtain ⟨K, hK_eq, hKnorm_L, hlK, -, hKset⟩ := inCalOStar_K_facts h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hKx : conjSubgroup K x = K :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L hxL)
  have hxK' : conjSubgroup V x ⊔ K = V ⊔ K := by rw [hK_eq]; exact hxK
  have hxinvK' : conjSubgroup V x⁻¹ ⊔ K = V ⊔ K := by
    have h1 := congrArg (fun H : Subgroup G => conjSubgroup H x⁻¹) hxK'
    rw [conjSubgroup_sup, conjSubgroup_sup, conjSubgroup_conjSubgroup, mul_inv_cancel,
      conjSubgroup_one,
      conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L ((LOf V g).inv_mem hxL))] at h1
    exact h1.symm
  have hVK : V ≤ Subgroup.normalizer (K : Set G) :=
    fun v hv => hKnorm_L (Subgroup.mem_sup_left hv)
  have stepGen : ∀ w ∈ LOf V g, conjSubgroup V w⁻¹ ⊔ K = V ⊔ K →
      ∀ u ∈ UOf M V g, w⁻¹ * u * w ∈ UOf M V g := by
    intro w hwL hwKinv u hu
    apply mem_U_of_commutator_le_N_of_ne hcopy hgen hUV
    · have hmem : w⁻¹ * u * w ∈ conjSubgroup K w := by
        rw [mem_conjSubgroup_iff]
        rw [show w * (w⁻¹ * u * w) * w⁻¹ = u by group]
        exact hK_eq ▸ Subgroup.mem_sup_left hu
      rw [conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L hwL)] at hmem
      simpa [hK_eq] using hmem
    · intro v hv
      have hvv : w * v * w⁻¹ ∈ V ⊔ K := by
        have hv1 : w * v * w⁻¹ ∈ conjSubgroup V w⁻¹ := by
          rw [mem_conjSubgroup_iff]
          rw [show (w⁻¹) * (w * v * w⁻¹) * (w⁻¹)⁻¹ = v by group]
          exact hv
        rw [← hwKinv]
        exact Subgroup.mem_sup_left hv1
      have hvv' : w * v * w⁻¹ ∈ (↑(V ⊔ K) : Set G) := hvv
      rw [Subgroup.coe_mul_of_left_le_normalizer_right V K hVK] at hvv'
      obtain ⟨v₁, hv₁V, k₁, hk₁K, hvv1⟩ := hvv'
      have key1 : ⁅u, v₁ * k₁⁆ ∈ NOf M V g := by
        rw [commutatorElement_mul_right_eq_mul_conj]
        have h1 : ⁅u, v₁⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.2 (IsElemAbelian.comm hV hu.1 hv₁V)
        have h2 : ⁅u, k₁⁆ ∈ NOf M V g :=
          commutator_U_sup_B_le_N hcopy
            (Subgroup.commutator_mem_commutator hu (hK_eq ▸ hk₁K))
        rw [h1, one_mul]
        have hcomm2 := Subgroup.mem_centralizer_iff.1 (NOf_le_centralizer_L hcopy h2) v₁
          (Subgroup.mem_sup_left hv₁V)
        rwa [show v₁ * ⁅u, k₁⁆ * v₁⁻¹ = ⁅u, k₁⁆ by rw [hcomm2]; group]
      have hxv : w * v * w⁻¹ = v₁ * k₁ := hvv1.symm
      have hfin : w⁻¹ * ⁅u, w * v * w⁻¹⁆ * w ∈ NOf M V g := by
        rw [hxv]
        have hc := Subgroup.mem_centralizer_iff.1 (NOf_le_centralizer_L hcopy key1) w⁻¹
          ((LOf V g).inv_mem hwL)
        rwa [show w⁻¹ * ⁅u, v₁ * k₁⁆ * w = ⁅u, v₁ * k₁⁆ by rw [hc]; group]
      have hconj : ⁅w⁻¹ * u * w, v⁆ = w⁻¹ * ⁅u, w * v * w⁻¹⁆ * w := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [hconj]
      exact hfin
  have step : ∀ u ∈ UOf M V g, x⁻¹ * u * x ∈ UOf M V g :=
    stepGen x hxL hxinvK'
  have step' : ∀ u ∈ UOf M V g, (x⁻¹)⁻¹ * u * x⁻¹ ∈ UOf M V g :=
    stepGen x⁻¹ ((LOf V g).inv_mem hxL) (by simpa using hxK')
  apply le_antisymm
  · intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have := step (x * y * x⁻¹) hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
  · intro u hu
    rw [mem_conjSubgroup_iff]
    simpa using step' u hu

theorem conjSubgroup_V_eq_of_sup_eq_of_ne {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) (hUV : UOf M V g ≠ V)
    {x : G} (hxL : x ∈ LOf V g)
    (hxK : conjSubgroup V x ⊔ (UOf M V g ⊔ BOf M V g)
      = V ⊔ (UOf M V g ⊔ BOf M V g)) :
    conjSubgroup V x = V := by
  have hcopy := h
  obtain ⟨K, hK_eq, hKnorm_L, hlK, -, hKset⟩ := inCalOStar_K_facts h
  obtain ⟨hV, hV0, hM, hM0, hTI, hN0, hg⟩ := h
  have hxle : conjSubgroup V x ≤ V ⊔ (UOf M V g ⊔ BOf M V g) := by
    rw [← hxK]; exact le_sup_left
  have hUx := conjSubgroup_U_eq_of_sup_eq_of_ne hcopy hgen hUV hxL hxK
  have hKx : conjSubgroup K x = K :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L hxL)
  have hXK : conjSubgroup V x ⊓ K = UOf M V g := by
    have hconj : conjSubgroup (V ⊓ K) x = conjSubgroup V x ⊓ K := by
      rw [conjSubgroup_inf, hKx]
    rw [V_inf_K_eq_U hcopy hKset, hUx] at hconj
    exact hconj.symm
  have hUB : UOf M V g ≤ Subgroup.normalizer (BOf M V g : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (commutator_U_B_le_N hcopy).trans inf_le_right
  have hBV : BOf M V g ≤ Subgroup.normalizer (V : Set G) := by
    intro b hb
    rw [hM]
    exact hb.2
  have hXea : IsElemAbelian 2 (conjSubgroup V x) := by
    simpa [conjSubgroup] using IsElemAbelian.map hV (MulAut.conj x⁻¹).toMonoidHom
  have hVgea : IsElemAbelian 2 (conjSubgroup V g) := by
    simpa [conjSubgroup] using IsElemAbelian.map hV (MulAut.conj g⁻¹).toMonoidHom
  have hXleV : conjSubgroup V x ≤ V := by
    intro y hy
    by_cases hyK : y ∈ K
    · have hy' : y ∈ conjSubgroup V x ⊓ K := ⟨hy, hyK⟩
      rw [hXK] at hy'
      exact (Subgroup.mem_inf.1 hy').1
    · have hyVB : y ∈ V ⊔ BOf M V g := by
        have h1 : y ∈ V ⊔ (UOf M V g ⊔ BOf M V g) := hxle hy
        have heq : V ⊔ (UOf M V g ⊔ BOf M V g) = V ⊔ BOf M V g := by
          apply le_antisymm
          · exact sup_le le_sup_left
              (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
          · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
        rwa [heq] at h1
      have hyVB' : y ∈ (↑(V ⊔ BOf M V g) : Set G) := hyVB
      rw [Subgroup.coe_mul_of_right_le_normalizer_left V (BOf M V g) hBV] at hyVB'
      obtain ⟨v, hvV, b, hbB, hvb⟩ := hyVB'
      have hvb' : v * b = y := hvb
      have hy2 : (v * b) * (v * b) = 1 := by
        rw [hvb']; exact IsElemAbelian.mul_self_eq_one hXea hy
      have hbb : b * b = 1 := IsElemAbelian.mul_self_eq_one hVgea hbB.1
      have hvv : v * v = 1 := IsElemAbelian.mul_self_eq_one hV hvV
      have hcomm : v * b = b * v := by
        have h1 : v * b * v * b = 1 := by simpa [mul_assoc] using hy2
        have h3 : v * b * v = b := by
          have := congrArg (fun z => z * b) h1
          simpa [mul_assoc, hbb] using this
        have hleft : v * (v * b * v) = v * b := by rw [h3]
        have hright : v * (v * b * v) = b * v := by
          calc v * (v * b * v) = (v * v) * (b * v) := by group
            _ = b * v := by rw [hvv, one_mul]
        exact (hright.symm.trans hleft).symm
      have hvb1 : ⁅v, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hcomm
      have hbv1 : ⁅b, v⁆ = 1 := by
        rw [show ⁅b, v⁆ = ⁅v, b⁆⁻¹ from (commutatorElement_inv v b).symm, hvb1, inv_one]
      have hvU : v ∉ UOf M V g := by
        intro hvU
        apply hyK
        have hmem : v * b ∈ (↑(UOf M V g ⊔ BOf M V g) : Set G) := by
          rw [Subgroup.coe_mul_of_left_le_normalizer_right (UOf M V g) (BOf M V g) hUB]
          exact ⟨v, hvU, b, hbB, rfl⟩
        rw [hvb'] at hmem
        rwa [← hK_eq] at hmem
      have hbU : b ∈ UOf M V g :=
        stepB hcopy hgen hvV hvU b (Subgroup.mem_sup_right hbB)
          (by rw [hbv1]; exact (NOf M V g).one_mem)
      rw [← hvb']
      exact V.mul_mem hvV (Subgroup.mem_inf.1 hbU).1
  exact Subgroup.eq_of_le_of_card_ge hXleV (by
    have hcard : Nat.card (conjSubgroup V x) = Nat.card V := by
      simpa [conjSubgroup] using Subgroup.card_map_of_injective (K := V)
        (f := (MulAut.conj x⁻¹).toMonoidHom) (MulAut.conj x⁻¹).injective
    rw [hcard])

theorem conjSubgroup_V_eq_conjSubgroup_V_of_sup_eq_of_ne {n : ℕ} {M V₀ V : Subgroup G}
    {g : G} (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) (hUV : UOf M V g ≠ V)
    {w : G} (hwL : w ∈ LOf V g)
    (hwK : conjSubgroup V w ⊔ (UOf M V g ⊔ BOf M V g)
      = conjSubgroup V g ⊔ (UOf M V g ⊔ BOf M V g)) :
    conjSubgroup V w = conjSubgroup V g := by
  obtain ⟨K, hK_eq, hKnorm_L, hlK, -, hKset⟩ := inCalOStar_K_facts h
  obtain ⟨l₀, hl₀L, hl₀V⟩ := hlK
  have hwK' : conjSubgroup V w ⊔ K = conjSubgroup V g ⊔ K := by rw [hK_eq]; exact hwK
  have hgl : conjSubgroup (conjSubgroup V g) l₀⁻¹ = V := by
    rw [hl₀V, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
  have hxL : w * l₀⁻¹ ∈ LOf V g := (LOf V g).mul_mem hwL ((LOf V g).inv_mem hl₀L)
  have hxK : conjSubgroup V (w * l₀⁻¹) ⊔ (UOf M V g ⊔ BOf M V g)
      = V ⊔ (UOf M V g ⊔ BOf M V g) := by
    have h1 := congrArg (fun H : Subgroup G => conjSubgroup H l₀⁻¹) hwK'
    rw [conjSubgroup_sup, conjSubgroup_sup,
      conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L ((LOf V g).inv_mem hl₀L))] at h1
    rw [conjSubgroup_conjSubgroup, hgl, hK_eq] at h1
    exact h1
  have hVx := conjSubgroup_V_eq_of_sup_eq_of_ne h hgen hUV hxL hxK
  have h2 : conjSubgroup V w = conjSubgroup V l₀ := by
    have h2 := congrArg (fun H : Subgroup G => conjSubgroup H l₀) hVx
    rw [conjSubgroup_conjSubgroup] at h2
    simpa [mul_assoc] using h2
  exact h2.trans hl₀V.symm

section Transport

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}

theorem eq_sup_of_coe_eq_mul {K U B : Subgroup G}
    (h : (K : Set G) = (B : Set G) * (U : Set G)) : K = U ⊔ B := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (B : Set G) * (U : Set G) := h ▸ hx
    obtain ⟨b, hb, u, hu, rfl⟩ := hx'
    exact (U ⊔ B).mul_mem (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left hu)
  · refine sup_le ?_ ?_
    · intro u hu
      have : u ∈ (B : Set G) * (U : Set G) := ⟨1, B.one_mem, u, hu, one_mul u⟩
      rwa [← h] at this
    · intro b hb
      have : b ∈ (B : Set G) * (U : Set G) := ⟨b, hb, 1, U.one_mem, mul_one b⟩
      rwa [← h] at this

theorem conjSubgroup_subgroupOf (H : Subgroup G) (w : ↥(LOf V g)) :
    conjSubgroup (H.subgroupOf (LOf V g)) w = (conjSubgroup H (w : G)).subgroupOf (LOf V g) := by
  ext y
  simp only [mem_conjSubgroup_iff, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

theorem map_conjSubgroup_of_hom {G' : Type} [Group G'] (f : G →* G')
    (A : Subgroup G) (x : G) :
    conjSubgroup (A.map f) (f x) = (conjSubgroup A x).map f := by
  ext q
  constructor
  · intro hq
    rw [mem_conjSubgroup_iff, Subgroup.mem_map] at hq
    obtain ⟨a, ha, haq⟩ := hq
    have hmem : x⁻¹ * a * x ∈ conjSubgroup A x := by
      rw [mem_conjSubgroup_iff]
      have heq : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
      rwa [heq]
    have himg : f (x⁻¹ * a * x) = q := by
      rw [map_mul, map_mul, map_inv, haq]; group
    exact Subgroup.mem_map.2 ⟨_, hmem, himg⟩
  · intro hq
    rw [Subgroup.mem_map] at hq
    obtain ⟨b, hb, hbq⟩ := hq
    rw [mem_conjSubgroup_iff]
    rw [← hbq]
    rw [mem_conjSubgroup_iff] at hb
    exact Subgroup.mem_map.2 ⟨x * b * x⁻¹, hb, by rw [map_mul, map_mul, map_inv]⟩

theorem sup_subgroupOf_eq_of_map_eq [hK : (K.subgroupOf (LOf V g)).Normal]
    {X Y : Subgroup ↥(LOf V g)}
    (h : X.map (QuotientGroup.mk' (K.subgroupOf (LOf V g))) =
         Y.map (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) :
    X ⊔ (K.subgroupOf (LOf V g)) = Y ⊔ (K.subgroupOf (LOf V g)) := by
  have h1 := congrArg (Subgroup.comap (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) h
  rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1

theorem card_map_subgroupOf_eq_relIndex (h : Hyp64 n M V₀ V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G)) :
    Nat.card ((V.subgroupOf (LOf V g)).map
        (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) = (UOf M V g).relIndex V := by
  let L := LOf V g
  let π : ↥L →* (↥L ⧸ (K.subgroupOf L)) := QuotientGroup.mk' (K.subgroupOf L)
  let ι : ↥V →* ↥L := Subgroup.inclusion (le_sup_left : V ≤ L)
  let f : ↥V →* (↥L ⧸ (K.subgroupOf L)) := π.comp ι
  have hrange : f.range = (V.subgroupOf L).map π := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map]
    congr 1
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.inclusion_range (le_sup_left : V ≤ L)
  have hker : f.ker = (UOf M V g).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' (K.subgroupOf L)) (ι v) = 1 ↔ (v : G) ∈ UOf M V g
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hvK
      rw [← V_inf_K_eq_U h hKset]
      exact ⟨v.2, hvK⟩
    · intro hvU
      rw [← V_inf_K_eq_U h hKset] at hvU
      exact hvU.2
  calc Nat.card ((V.subgroupOf L).map π) = Nat.card f.range := by rw [hrange]
    _ = (f.ker).index :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm
    _ = ((UOf M V g).subgroupOf V).index := by rw [hker]
    _ = (UOf M V g).relIndex V := rfl

theorem isElemAbelian_map_subgroupOf (h : Hyp64 n M V₀ V g)
    [hK : (K.subgroupOf (LOf V g)).Normal] :
    IsElemAbelian 2 ((V.subgroupOf (LOf V g)).map
      (QuotientGroup.mk' (K.subgroupOf (LOf V g)))) :=
  IsElemAbelian.map (h.elemAbelian.subgroupOf (LOf V g)) _

theorem map_subgroupOf_sup_eq_top (h : Hyp64 n M V₀ V g)
    [hK : (K.subgroupOf (LOf V g)).Normal] :
    (V.subgroupOf (LOf V g)).map (QuotientGroup.mk' (K.subgroupOf (LOf V g))) ⊔
        ((conjSubgroup V g).subgroupOf (LOf V g)).map
          (QuotientGroup.mk' (K.subgroupOf (LOf V g))) = ⊤ := by
  rw [← Subgroup.map_sup]
  have hsup : (V.subgroupOf (LOf V g)) ⊔ ((conjSubgroup V g).subgroupOf (LOf V g)) = ⊤ := by
    change (V.subgroupOf (V ⊔ conjSubgroup V g)) ⊔
      ((conjSubgroup V g).subgroupOf (V ⊔ conjSubgroup V g)) = ⊤
    rw [← Subgroup.subgroupOf_sup (le_sup_left : V ≤ V ⊔ conjSubgroup V g)
      (le_sup_right : conjSubgroup V g ≤ V ⊔ conjSubgroup V g)]
    exact Subgroup.subgroupOf_self _
  rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem map_subgroupOf_ne_bot (h : Hyp64 n M V₀ V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G)) :
    (V.subgroupOf (LOf V g)).map
      (QuotientGroup.mk' (K.subgroupOf (LOf V g))) ≠ ⊥ := by
  intro hbot
  have hle : V.subgroupOf (LOf V g) ≤ K.subgroupOf (LOf V g) := by
    have h1 : V.subgroupOf (LOf V g) ≤ (QuotientGroup.mk' (K.subgroupOf (LOf V g))).ker :=
      (Subgroup.map_eq_bot_iff (V.subgroupOf (LOf V g))).1 hbot
    rwa [QuotientGroup.ker_mk'] at h1
  have hVK : V ≤ K := by
    intro v hv
    have hx : (⟨v, (le_sup_left : V ≤ LOf V g) hv⟩ : ↥(LOf V g)) ∈ V.subgroupOf (LOf V g) := hv
    exact hle hx
  have hVeq : V = UOf M V g := by
    rw [← V_inf_K_eq_U h hKset]
    exact le_antisymm (le_inf le_rfl hVK) inf_le_left
  exact h.inCalOStar.1.2.1 (hVeq ▸ inf_le_right)

end Transport

section Dihedral

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G} {K : Subgroup G}

theorem relIndex_two_of_dihedral (h : Hyp64 n M V₀ V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hdi : ∃ m : ℕ, Odd m ∧
      Nonempty ((↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) ≃* DihedralGroup m)) :
    (UOf M V g).relIndex V = 2 := by
  obtain ⟨m, hm, ⟨e⟩⟩ := hdi
  let L := LOf V g
  haveI : (K.subgroupOf L).Normal := hK
  let π : ↥L →* (↥L ⧸ (K.subgroupOf L)) := QuotientGroup.mk' (K.subgroupOf L)
  let A : Subgroup (↥L ⧸ (K.subgroupOf L)) := (V.subgroupOf L).map π
  have hAcard : Nat.card A = (UOf M V g).relIndex V :=
    card_map_subgroupOf_eq_relIndex h hKset
  have hAea : IsElemAbelian 2 A := isElemAbelian_map_subgroupOf (K := K) h
  have hAle : Nat.card A ≤ 2 := by
    have h1 : Nat.card (A.map e.toMonoidHom) ≤ 2 :=
      nat_card_le_two_of_isElemAbelian_dihedral hm (hAea.map e.toMonoidHom)
    rwa [Subgroup.card_map_of_injective e.injective] at h1
  have hAne : A ≠ ⊥ := map_subgroupOf_ne_bot (K := K) h hKset
  have hAge2 : 2 ≤ Nat.card A := by
    have h2 := (Subgroup.one_lt_card_iff_ne_bot A).2 hAne
    omega
  have hAcard2 : Nat.card A = 2 := le_antisymm hAle hAge2
  rw [← hAcard, hAcard2]

theorem genHyp_of_dihedral (h : Hyp64 n M V₀ V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hdi : ∃ m : ℕ, Odd m ∧
      Nonempty ((↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) ≃* DihedralGroup m)) :
    GenHyp M V g :=
  genHyp_of_relIndex_two h (relIndex_two_of_dihedral (hK := hK) h hKset hdi)

theorem swapHyp_of_dihedral (h : Hyp64 n M V₀ V g)
    [hK : (K.subgroupOf (LOf V g)).Normal]
    (hKset : (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G))
    (hdi : ∃ m : ℕ, Odd m ∧
      Nonempty ((↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) ≃* DihedralGroup m)) :
    SwapHyp V g := by
  classical
  have hrel : (UOf M V g).relIndex V = 2 :=
    relIndex_two_of_dihedral (hK := hK) h hKset hdi
  have hgen : GenHyp M V g := genHyp_of_dihedral (hK := hK) h hKset hdi
  obtain ⟨m, hm, ⟨e⟩⟩ := hdi
  let L := LOf V g
  haveI : (K.subgroupOf L).Normal := hK
  let π : ↥L →* (↥L ⧸ (K.subgroupOf L)) := QuotientGroup.mk' (K.subgroupOf L)
  let A : Subgroup (↥L ⧸ (K.subgroupOf L)) := (V.subgroupOf L).map π
  let Bq : Subgroup (↥L ⧸ (K.subgroupOf L)) := ((conjSubgroup V g).subgroupOf L).map π
  have hAea : IsElemAbelian 2 A := isElemAbelian_map_subgroupOf (K := K) h
  have hAne : A ≠ ⊥ := map_subgroupOf_ne_bot (K := K) h hKset
  obtain ⟨-, K', hK'norm, hK'set, hQuot, hlK, -⟩ := h.inCalOStar
  obtain ⟨l, hlL, hlV⟩ := hlK
  have hAleB : conjSubgroup A (π ⟨l, hlL⟩) = Bq := by
    rw [show A = (V.subgroupOf L).map π from rfl, map_conjSubgroup_of_hom,
      conjSubgroup_subgroupOf, ← hlV]
  have ha : ∃ a ∈ A, a ≠ 1 ∧ a * a = 1 := by
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAne
    refine ⟨(a : ↥L ⧸ (K.subgroupOf L)), a.2, fun hh => ha1 (Subtype.ext hh), ?_⟩
    exact IsElemAbelian.mul_self_eq_one hAea a.2
  obtain ⟨z, hz2, hzconj⟩ :=
    exists_involution_conj_of_dihedral hm e hAleB ha
  obtain ⟨w, hwπ⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) z
  have hwK : conjSubgroup V (w : G) ⊔ (UOf M V g ⊔ BOf M V g)
      = conjSubgroup V g ⊔ (UOf M V g ⊔ BOf M V g) := by
    have hAB : (conjSubgroup (V.subgroupOf L) w).map π
        = ((conjSubgroup V g).subgroupOf L).map π := by
      rw [← map_conjSubgroup_of_hom, hwπ, hzconj]
    have hsup := sup_subgroupOf_eq_of_map_eq (K := K) hAB
    have hmap := congrArg (Subgroup.map L.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_sup, conjSubgroup_subgroupOf] at hmap
    have hVwL : conjSubgroup V (w : G) ≤ LOf V g :=
      (conjSubgroup_mono (le_sup_left : V ≤ LOf V g) (w : G)).trans
        (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer w.2)))
    have hVw : (((conjSubgroup V (w : G)).subgroupOf L).map L.subtype) = conjSubgroup V (w : G) :=
      Subgroup.map_subgroupOf_eq_of_le hVwL
    have hVs : (((conjSubgroup V g).subgroupOf L).map L.subtype) = conjSubgroup V g :=
      Subgroup.map_subgroupOf_eq_of_le (le_sup_right : conjSubgroup V g ≤ LOf V g)
    have hLsub : ((K.subgroupOf L).map L.subtype) = K := by
      refine Subgroup.map_subgroupOf_eq_of_le ?_
      rw [eq_sup_of_coe_eq_mul hKset]
      exact sup_le (fun u hu => Subgroup.mem_sup_left hu.1)
        (fun b hb => Subgroup.mem_sup_right hb.1)
    rw [hVw, hVs, hLsub] at hmap
    rw [← eq_sup_of_coe_eq_mul hKset]
    exact hmap
  have hw2 : (w : G) * (w : G) ∈ UOf M V g ⊔ BOf M V g := by
    have h1 : (w * w : ↥L) ∈ (QuotientGroup.mk' (K.subgroupOf L)).ker := by
      rw [MonoidHom.mem_ker, map_mul, hwπ, hz2]
    rw [QuotientGroup.ker_mk'] at h1
    have h2 : ((w * w : ↥L) : G) ∈ K := h1
    rw [← eq_sup_of_coe_eq_mul hKset]
    exact h2
  exact swapHyp_of_sup_eq_and_mem h hgen hrel w.2 hwK hw2

@[expose] def DihedralShape (M V₀ V : Subgroup G) (g : G) : Prop :=
  ∃ K : Subgroup G, ∃ _ : (K.subgroupOf (LOf V g)).Normal,
    (K : Set G) = ((BOf M V g : Subgroup G) : Set G) *
      ((UOf M V g : Subgroup G) : Set G) ∧
    ∃ m : ℕ, Odd m ∧
      Nonempty ((↥(LOf V g) ⧸ (K.subgroupOf (LOf V g))) ≃* DihedralGroup m)

theorem six_four_four_centralizer_B_of_dihedral {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hdi : DihedralShape M V₀ V g) :
    BOf M V g ⊓ F11.CTilde M V₀ V = NOf M V g ⊔ conjSubgroup V₀ g := by
  obtain ⟨K, hKnorm, hKset, hdi'⟩ := hdi
  exact six_four_four_centralizer_B_of_relIndex_two h
    (relIndex_two_of_dihedral (hK := hKnorm) h hKset hdi')

theorem six_four_five_of_dihedral {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hdi : DihedralShape M V₀ V g) :
    (BOf M V g ⊓ F11.CTilde M V₀ V).relIndex (BOf M V g)
        * (UOf M V g).relIndex V
      = (V ⊓ Subgroup.centralizer (BOf M V g : Set G)).relIndex V := by
  obtain ⟨K, hKnorm, hKset, hdi'⟩ := hdi
  exact six_four_five_of_relIndex_two h
    (relIndex_two_of_dihedral (hK := hKnorm) h hKset hdi')

end Dihedral

end CFSG.LocalAnalysis.WeakClosure81
