module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral

public section

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type*} [Group G] [Finite G]

lemma h2_perfect_top {K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
  have hmap : Subgroup.map K.subtype (⊤ : Subgroup K) = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
  rw [Subgroup.map_commutator, hmap]
  exact hK

lemma h2_eq_one_of_solvable_perfect {D : Type*} [Group D] [Group.IsSolvable D]
    (hD : ⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆ = ⊤) (d : D) : d = 1 := by
  have hder : ∀ n : ℕ, derivedSeries D n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, hD]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, derivedSeries D n = ⊥ := Group.IsSolvable.solvable
  have htb : (⊤ : Subgroup D) = ⊥ := by rw [← hder n, hn]
  have hd : d ∈ (⊥ : Subgroup D) := by
    rw [← htb]
    exact Subgroup.mem_top d
  exact Subgroup.mem_bot.mp hd

lemma h2_perf_solv {A B Q : Type*} [Group A] [Group B] [Group Q] [Group.IsSolvable B]
    (hA : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤) (f : A →* Q) (g : B →* Q)
    (h : ∀ a : A, ∃ b : B, g b = f a) (a : A) : f a = 1 := by
  have hle : f.range ≤ g.range := by
    rintro _ ⟨a', rfl⟩
    obtain ⟨b, hb⟩ := h a'
    exact ⟨b, hb⟩
  haveI : Group.IsSolvable g.range := Group.isSolvable_of_surjective g.rangeRestrict_surjective
  haveI : Group.IsSolvable f.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hR : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hA]
  have hmap : Subgroup.map f.range.subtype (⊤ : Subgroup f.range) = f.range := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hD : ⁅(⊤ : Subgroup f.range), (⊤ : Subgroup f.range)⁆ = ⊤ := by
    apply Subgroup.map_injective (f := f.range.subtype) f.range.subtype_injective
    rw [Subgroup.map_commutator, hmap]
    exact hR
  have hel := h2_eq_one_of_solvable_perfect hD ⟨f a, ⟨a, rfl⟩⟩
  exact congrArg Subtype.val hel

lemma h2_inv_centr {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y * s * y⁻¹ = s) :
    ∀ s ∈ S, y⁻¹ * s * y = s := by
  intro s hs
  have hcomm : y * s = s * y := by
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [hy s hs]
  calc y⁻¹ * s * y = y⁻¹ * (s * y) := by group
    _ = y⁻¹ * (y * s) := by rw [hcomm]
    _ = s := by group

lemma h2_comm_centr {S : Subgroup G} {y g : G} (hy : ∀ s ∈ S, y * s * y⁻¹ = s)
    (hg : ∀ s ∈ S, g⁻¹ * s * g ∈ S) :
    ∀ s ∈ S, (y * g * y⁻¹ * g⁻¹) * s * (y * g * y⁻¹ * g⁻¹)⁻¹ = s := by
  intro s hs
  have hinv := h2_inv_centr hy
  calc y * g * y⁻¹ * g⁻¹ * s * (y * g * y⁻¹ * g⁻¹)⁻¹
      = y * (g * (y⁻¹ * (g⁻¹ * s * g) * y) * g⁻¹) * y⁻¹ := by group
    _ = y * (g * (g⁻¹ * s * g) * g⁻¹) * y⁻¹ := by rw [hinv _ (hg s hs)]
    _ = y * s * y⁻¹ := by group
    _ = s := hy s hs

lemma h2_mem_normalizer_of_centr {S : Subgroup G} {y : G} (hy : ∀ s ∈ S, y * s * y⁻¹ = s) :
    y ∈ Subgroup.normalizer (S : Set G) := by
  have hinv := h2_inv_centr hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hy x hx]
    exact hx
  · intro hx
    have h2 := hinv _ hx
    have h3 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rw [h3] at h2
    rw [h2]
    exact hx

lemma h2_conj_inv_mem {S : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G))
    {s : G} (hs : s ∈ S) : g⁻¹ * s * g ∈ S := by
  have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set G)).inv_mem hg) s).mp hs
  rwa [inv_inv] at h

lemma h2_witness {S θ : Subgroup G} {X Y u : G} (hY : Y = u * X)
    (hYc : ∀ s ∈ S, Y * s * Y⁻¹ = s) (hu : u ∈ θ) (hX : X ∈ Subgroup.normalizer (S : Set G)) :
    ∃ n ∈ θ, n ∈ Subgroup.normalizer (S : Set G) ∧ ∀ s ∈ S, X * s * X⁻¹ = n * s * n⁻¹ := by
  have hYN : Y ∈ Subgroup.normalizer (S : Set G) := h2_mem_normalizer_of_centr hYc
  have hinv : u⁻¹ = X * Y⁻¹ := by rw [hY]; group
  refine ⟨u⁻¹, θ.inv_mem hu, ?_, fun s hs => ?_⟩
  · rw [hinv]
    exact (Subgroup.normalizer (S : Set G)).mul_mem hX ((Subgroup.normalizer (S : Set G)).inv_mem hYN)
  · have hXeq : X = u⁻¹ * Y := by rw [hY, inv_mul_cancel_left]
    rw [inv_inv, hXeq]
    calc u⁻¹ * Y * s * (u⁻¹ * Y)⁻¹ = u⁻¹ * (Y * s * Y⁻¹) * u := by group
      _ = u⁻¹ * s * u := by rw [hYc s hs]

abbrev h2_act (S A : Subgroup G) (hA : A ≤ Subgroup.normalizer (S : Set G)) : MulAction A S where
  smul a s := ⟨(a : G) * (s : G) * (a : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hA a.2) (s : G)).mp s.2⟩
  one_smul s := by
    apply Subtype.ext
    show ((1 : A) : G) * (s : G) * ((1 : A) : G)⁻¹ = (s : G)
    simp
  mul_smul a b s := by
    apply Subtype.ext
    show ((a * b : A) : G) * (s : G) * ((a * b : A) : G)⁻¹ =
      (a : G) * ((b : G) * (s : G) * (b : G)⁻¹) * (a : G)⁻¹
    simp only [Subgroup.coe_mul]
    group

theorem five_nc_lemma {θ H S K : Subgroup G} [(θ.subgroupOf K).Normal]
    (hθH : θ ≤ H) (hHθ : H ≤ normalizer (θ : Set G)) (hθs : Group.IsSolvable θ)
    (hKH : K ≤ H) (hKS : K ≤ normalizer (S : Set G)) (hperf : ⁅K, K⁆ = K)
    (hsimp : IsSimpleGroup (K ⧸ θ.subgroupOf K)) (hnt : ∃ k ∈ K, ∃ s ∈ S, k * s * k⁻¹ ≠ s)
    {k m y : G} (hk : k ∈ K) (hm : m ∈ H) (hmK : ∀ g ∈ K, ⁅m, g⁆ ∈ θ)
    (hy : (k * m)⁻¹ * y ∈ θ) (hyS : ∀ s ∈ S, y * s * y⁻¹ = s) : k ∈ θ := by
  have hKperf' : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := h2_perfect_top hperf
  have hθconj : ∀ x ∈ H, ∀ z ∈ θ, x * z * x⁻¹ ∈ θ := fun x hx z hz =>
    (Subgroup.mem_normalizer_iff.mp (hHθ hx) z).mp hz
  obtain ⟨t, ht, rfl⟩ : ∃ t ∈ θ, y = k * m * t := ⟨(k * m)⁻¹ * y, hy, by group⟩
  obtain ⟨L, hL⟩ : ∃ L : Subgroup G, ∀ g : G, g ∈ L ↔ g ∈ K ∧ ∃ n ∈ θ,
      n ∈ Subgroup.normalizer (S : Set G) ∧ ∀ s ∈ S, g * s * g⁻¹ = n * s * n⁻¹ := by
    refine ⟨{ carrier := {g | g ∈ K ∧ ∃ n ∈ θ, n ∈ Subgroup.normalizer (S : Set G) ∧
                ∀ s ∈ S, g * s * g⁻¹ = n * s * n⁻¹},
              mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · rintro a b ⟨ha, n1, hn1θ, hn1N, hn1⟩ ⟨hb, n2, hn2θ, hn2N, hn2⟩
      show _ ∧ _
      refine ⟨K.mul_mem ha hb, n1 * n2, θ.mul_mem hn1θ hn2θ,
        (Subgroup.normalizer (S : Set G)).mul_mem hn1N hn2N, ?_⟩
      intro s hs
      have hs2 : n2 * s * n2⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hn2N s).mp hs
      calc a * b * s * (a * b)⁻¹ = a * (b * s * b⁻¹) * a⁻¹ := by group
        _ = a * (n2 * s * n2⁻¹) * a⁻¹ := by rw [hn2 s hs]
        _ = n1 * (n2 * s * n2⁻¹) * n1⁻¹ := hn1 _ hs2
        _ = n1 * n2 * s * (n1 * n2)⁻¹ := by group
    · show _ ∧ _
      exact ⟨K.one_mem, 1, θ.one_mem, (Subgroup.normalizer (S : Set G)).one_mem,
        fun s _ => by simp⟩
    · rintro a ⟨ha, n, hnθ, hnN, hn⟩
      show _ ∧ _
      refine ⟨K.inv_mem ha, n⁻¹, θ.inv_mem hnθ,
        (Subgroup.normalizer (S : Set G)).inv_mem hnN, ?_⟩
      intro s hs
      have e := hn _ (h2_conj_inv_mem (hKS ha) hs)
      simp only [inv_inv]
      calc a⁻¹ * s * a = n⁻¹ * (n * (a⁻¹ * s * a) * n⁻¹) * n := by group
        _ = n⁻¹ * (a * (a⁻¹ * s * a) * a⁻¹) * n := by rw [e]
        _ = n⁻¹ * s * n := by group
  have hLK : ∀ g ∈ L, g ∈ K := fun g hg => ((hL g).mp hg).1
  have hθKL : ∀ x ∈ θ, x ∈ K → x ∈ L := fun x hxθ hxK =>
    (hL x).mpr ⟨hxK, x, hxθ, hKS hxK, fun s _ => rfl⟩
  have hLconj : ∀ g ∈ K, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    obtain ⟨hlK, n, hnθ, hnN, hn⟩ := (hL l).mp hl
    refine (hL _).mpr ⟨K.mul_mem (K.mul_mem hg hlK) (K.inv_mem hg), g * n * g⁻¹,
      hθconj g (hKH hg) n hnθ, ?_, ?_⟩
    · exact (Subgroup.normalizer (S : Set G)).mul_mem
        ((Subgroup.normalizer (S : Set G)).mul_mem (hKS hg) hnN)
        ((Subgroup.normalizer (S : Set G)).inv_mem (hKS hg))
    · intro s hs
      have e := hn _ (h2_conj_inv_mem (hKS hg) hs)
      calc g * l * g⁻¹ * s * (g * l * g⁻¹)⁻¹ = g * (l * (g⁻¹ * s * g) * l⁻¹) * g⁻¹ := by group
        _ = g * (n * (g⁻¹ * s * g) * n⁻¹) * g⁻¹ := by rw [e]
        _ = g * n * g⁻¹ * s * (g * n * g⁻¹)⁻¹ := by group
  haveI hLn : (L.subgroupOf K).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have h := hLconj (g : G) g.2 (x : G) hx
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h⟩
  haveI hI : ((L.subgroupOf K).map (QuotientGroup.mk' (θ.subgroupOf K))).Normal :=
    Subgroup.Normal.map hLn (QuotientGroup.mk' (θ.subgroupOf K))
      (QuotientGroup.mk'_surjective (θ.subgroupOf K))
  rcases Subgroup.Normal.eq_bot_or_eq_top
      ((L.subgroupOf K).map (QuotientGroup.mk' (θ.subgroupOf K))) with hbot | htop
  ·
    have hLθ : ∀ l ∈ L, l ∈ θ := by
      intro l hl
      have hmem : QuotientGroup.mk' (θ.subgroupOf K) (⟨l, hLK l hl⟩ : K) ∈
          (L.subgroupOf K).map (QuotientGroup.mk' (θ.subgroupOf K)) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := θ.subgroupOf K) _).mp hmem)
    have hstep3 : ∀ g ∈ K, k * g * k⁻¹ * g⁻¹ ∈ θ := by
      intro g hg
      have hkm : k * m ∈ H := H.mul_mem (hKH hk) hm
      have hgt : g * t⁻¹ * g⁻¹ ∈ θ := hθconj g (hKH hg) t⁻¹ (θ.inv_mem ht)
      have hd : t * g * t⁻¹ * g⁻¹ ∈ θ := by
        simpa only [mul_assoc] using θ.mul_mem ht hgt
      have hU : k * m * (t * g * t⁻¹ * g⁻¹) * (k * m)⁻¹ * (k * (m * g * m⁻¹ * g⁻¹) * k⁻¹) ∈ θ :=
        θ.mul_mem (hθconj (k * m) hkm _ hd) (hθconj k (hKH hk) _ (hmK g hg))
      have hY : k * m * t * g * (k * m * t)⁻¹ * g⁻¹ =
          (k * m * (t * g * t⁻¹ * g⁻¹) * (k * m)⁻¹ * (k * (m * g * m⁻¹ * g⁻¹) * k⁻¹)) *
            (k * g * k⁻¹ * g⁻¹) := by
        group
      have hXK : k * g * k⁻¹ * g⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem (K.mul_mem hk hg) (K.inv_mem hk)) (K.inv_mem hg)
      exact hLθ _ ((hL _).mpr ⟨hXK, h2_witness hY
        (h2_comm_centr hyS (fun s hs => h2_conj_inv_mem (hKS hg) hs)) hU (hKS hXK)⟩)
    have hcent : ∀ g ∈ K, (g * k)⁻¹ * (k * g) ∈ θ := by
      intro g hg
      have h1 : k * g⁻¹ * k⁻¹ * g ∈ θ := by
        simpa only [inv_inv] using hstep3 g⁻¹ (K.inv_mem hg)
      have h2 := hθconj k⁻¹ (H.inv_mem (hKH hk)) _ (θ.inv_mem h1)
      have e : (g * k)⁻¹ * (k * g) = k⁻¹ * (k * g⁻¹ * k⁻¹ * g)⁻¹ * k⁻¹⁻¹ := by group
      rw [e]
      exact h2
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (K ⧸ θ.subgroupOf K)) with hc | hc
    · have hmkc : (QuotientGroup.mk (⟨k, hk⟩ : K) : K ⧸ θ.subgroupOf K) ∈
          Subgroup.center (K ⧸ θ.subgroupOf K) := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        exact hcent g' g'.2
      rw [hc, Subgroup.mem_bot] at hmkc
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (N := θ.subgroupOf K) _).mp hmkc)
    · exfalso
      have hQc : ∀ x y : K ⧸ θ.subgroupOf K, x * y = y * x := by
        intro x y
        have hx : x ∈ Subgroup.center (K ⧸ θ.subgroupOf K) := by
          rw [hc]
          exact Subgroup.mem_top x
        exact ((Subgroup.mem_center_iff.mp hx) y).symm
      have hcomm' : ∀ a b : K, ⁅a, b⁆ ∈ θ.subgroupOf K := by
        intro a b
        have h1 : QuotientGroup.mk' (θ.subgroupOf K) ⁅a, b⁆ = 1 := by
          rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          exact hQc _ _
        exact (QuotientGroup.eq_one_iff _).mp h1
      have htop' : (⊤ : Subgroup K) ≤ θ.subgroupOf K := by
        rw [← hKperf', Subgroup.commutator_le]
        intro a _ b _
        exact hcomm' a b
      have hall : ∀ z : K ⧸ θ.subgroupOf K, z = 1 := by
        intro z
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
        exact (QuotientGroup.eq_one_iff (N := θ.subgroupOf K) a).mpr (htop' (Subgroup.mem_top a))
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (K ⧸ θ.subgroupOf K)
      exact hxy ((hall x).trans (hall y).symm)
  ·
    exfalso
    have hKL : ∀ x ∈ K, x ∈ L := by
      intro x hx
      have hmem : QuotientGroup.mk' (θ.subgroupOf K) (⟨x, hx⟩ : K) ∈
          (L.subgroupOf K).map (QuotientGroup.mk' (θ.subgroupOf K)) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨l, hl, hleq⟩ := Subgroup.mem_map.mp hmem
      have hrel : (l : G)⁻¹ * x ∈ θ := by
        have h1 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq (s := θ.subgroupOf K)).mp hleq)
        exact h1
      have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
      have hxL : (l : G)⁻¹ * x ∈ L :=
        hθKL _ hrel (K.mul_mem (K.inv_mem (hLK _ hlL)) hx)
      have h2 := L.mul_mem hlL hxL
      rwa [mul_inv_cancel_left] at h2
    obtain ⟨T, hTmem⟩ : ∃ T : Subgroup G, ∀ n : G,
        n ∈ T ↔ n ∈ θ ∧ n ∈ Subgroup.normalizer (S : Set G) :=
      ⟨θ ⊓ Subgroup.normalizer (S : Set G), fun n => Subgroup.mem_inf⟩
    have hTN : T ≤ Subgroup.normalizer (S : Set G) := fun n hn => ((hTmem n).mp hn).2
    have hTθ : T ≤ θ := fun n hn => ((hTmem n).mp hn).1
    letI hKact : MulAction K S := h2_act S K hKS
    letI hTact : MulAction T S := h2_act S T hTN
    haveI hTsolv : Group.IsSolvable T :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hTθ)
    have hcov : ∀ a : K, ∃ b : T,
        (MulAction.toPermHom T S) b = (MulAction.toPermHom K S) a := by
      rintro ⟨x, hx⟩
      obtain ⟨-, n, hnθ, hnN, hn⟩ := (hL x).mp (hKL x hx)
      refine ⟨⟨n, (hTmem n).mpr ⟨hnθ, hnN⟩⟩, Equiv.ext fun s => Subtype.ext ?_⟩
      exact (hn (s : G) s.2).symm
    have hK1 : ∀ a : K, (MulAction.toPermHom K S) a = 1 := fun a =>
      h2_perf_solv hKperf' (MulAction.toPermHom K S) (MulAction.toPermHom T S) hcov a
    obtain ⟨k0, hk0, s0, hs0, hne⟩ := hnt
    have h1 : ((MulAction.toPermHom K S (⟨k0, hk0⟩ : K)) ⟨s0, hs0⟩ : G) = s0 := by
      rw [hK1 ⟨k0, hk0⟩]
      rfl
    have h2 : ((MulAction.toPermHom K S (⟨k0, hk0⟩ : K)) ⟨s0, hs0⟩ : G) = k0 * s0 * k0⁻¹ := rfl
    exact hne (h2.symm.trans h1)

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type*} [Group G] [Finite G]

theorem exists_five_element_not_mem {θ K : Subgroup G} [(θ.subgroupOf K).Normal]
    (h5 : 5 ∣ Nat.card (K ⧸ θ.subgroupOf K)) : ∃ x ∈ K, x ∉ θ ∧ IsPGroup 5 (Subgroup.zpowers x) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite (K ⧸ θ.subgroupOf K) := inferInstance
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := K ⧸ θ.subgroupOf K) 5 h5
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (θ.subgroupOf K) q
  have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨a, m, hpm, hyeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 5 (by norm_num)
  have hm0 : m ≠ 0 := fun h => hpm (by rw [h]; exact dvd_zero 5)
  have hmdvd : m ∣ orderOf y := ⟨5 ^ a, by rw [hyeq]; ring⟩
  have hxord : orderOf (y ^ m) = 5 ^ a := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hyeq, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hPg : IsPGroup 5 (Subgroup.zpowers ((y ^ m : K) : G)) :=
    IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord])
  refine ⟨((y ^ m : K) : G), (y ^ m).2, ?_, hPg⟩
  intro hmem
  have hmemK : y ^ m ∈ θ.subgroupOf K := Subgroup.mem_subgroupOf.mpr hmem
  have h1 : (QuotientGroup.mk' (θ.subgroupOf K)) (y ^ m) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmemK
  rw [map_pow] at h1
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hq] at hdvd
  exact hpm hdvd

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type*} [Group G] [Finite G]

theorem h4_pow_of_zpowers {H : Type*} [Group H] {x : H}
    (hx : IsPGroup 5 (Subgroup.zpowers x)) : ∃ k : ℕ, x ^ 5 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hx ⟨x, Subgroup.mem_zpowers x⟩
  refine ⟨k, ?_⟩
  have h := congrArg Subtype.val hk
  simpa using h

theorem h4_conj_mem {X : Type*} [Group X] (K : Subgroup X) {g h : X} (hg : g ∈ K) :
    h ∈ K ↔ g * h * g⁻¹ ∈ K := by
  constructor
  · intro hh
    exact K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg)
  · intro hh
    have h2 := K.mul_mem (K.mul_mem (K.inv_mem hg) hh) hg
    rwa [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at h2

theorem h4_mem_normalizer_inf {X : Type*} [Group X] {θ S : Subgroup X} {g : X}
    (hgθ : g ∈ Subgroup.normalizer (θ : Set X)) (hgS : g ∈ Subgroup.normalizer (S : Set X)) :
    g ∈ Subgroup.normalizer ((θ ⊓ Subgroup.normalizer (S : Set X) : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp hgθ h) (h4_conj_mem _ hgS)

theorem h4_comm_of_gen {Q : Type*} [Group Q] {a b : Q} (hab : a * b = b * a)
    (hgen : ∀ q : Q, q ∈ Subgroup.closure ({a, b} : Set Q)) :
    ∀ q r : Q, q * r = r * q := by
  have ha : ∀ q : Q, a * q = q * a := by
    intro q
    have hle : Subgroup.closure ({a, b} : Set Q) ≤ Subgroup.centralizer ({a} : Set Q) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      rcases hx with hx | hx
      · rw [hx]
      · rw [hx]; exact hab
    exact Subgroup.mem_centralizer_iff.mp (hle (hgen q)) a (Set.mem_singleton a)
  have hb : ∀ q : Q, b * q = q * b := by
    intro q
    have hle : Subgroup.closure ({a, b} : Set Q) ≤ Subgroup.centralizer ({b} : Set Q) := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      rcases hx with hx | hx
      · rw [hx]; exact hab.symm
      · rw [hx]
    exact Subgroup.mem_centralizer_iff.mp (hle (hgen q)) b (Set.mem_singleton b)
  intro q r
  have hle : Subgroup.closure ({a, b} : Set Q) ≤ Subgroup.centralizer ({q} : Set Q) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    rcases hx with hx | hx
    · rw [hx]; exact (ha q).symm
    · rw [hx]; exact (hb q).symm
  exact Subgroup.mem_centralizer_iff.mp (hle (hgen r)) q (Set.mem_singleton q)

theorem h4_isPGroup_of_gen {Q : Type*} [Group Q] {a b : Q} (ha : ∃ k : ℕ, a ^ 5 ^ k = 1)
    (hb : ∃ k : ℕ, b ^ 5 ^ k = 1) (hab : a * b = b * a)
    (hgen : ∀ q : Q, q ∈ Subgroup.closure ({a, b} : Set Q)) : IsPGroup 5 Q := by
  have hcomm := h4_comm_of_gen hab hgen
  have hmul : ∀ q r : Q, (∃ k : ℕ, q ^ 5 ^ k = 1) → (∃ k : ℕ, r ^ 5 ^ k = 1) →
      ∃ k : ℕ, (q * r) ^ 5 ^ k = 1 := by
    rintro q r ⟨k₁, hq⟩ ⟨k₂, hr⟩
    refine ⟨k₁ + k₂, ?_⟩
    have e1 : q ^ 5 ^ (k₁ + k₂) = 1 := by
      rw [pow_add (5 : ℕ) k₁ k₂, pow_mul, hq, one_pow]
    have e2 : r ^ 5 ^ (k₁ + k₂) = 1 := by
      rw [pow_add (5 : ℕ) k₁ k₂, mul_comm ((5 : ℕ) ^ k₁) ((5 : ℕ) ^ k₂), pow_mul, hr, one_pow]
    rw [(show Commute q r from hcomm q r).mul_pow, e1, e2, one_mul]
  have hinv : ∀ q : Q, (∃ k : ℕ, q ^ 5 ^ k = 1) → ∃ k : ℕ, q⁻¹ ^ 5 ^ k = 1 := by
    rintro q ⟨k, hk⟩
    exact ⟨k, by rw [inv_pow, hk, inv_one]⟩
  have hone : ∃ k : ℕ, (1 : Q) ^ 5 ^ k = 1 := ⟨0, by rw [one_pow]⟩
  obtain ⟨T, hT⟩ : ∃ T : Subgroup Q, ∀ q : Q, q ∈ T ↔ ∃ k : ℕ, q ^ 5 ^ k = 1 := by
    refine ⟨{ carrier := {q | ∃ k : ℕ, q ^ 5 ^ k = 1}
              mul_mem' := fun {x y} hx hy => hmul x y hx hy
              one_mem' := hone
              inv_mem' := fun {x} hx => hinv x hx }, fun q => Iff.rfl⟩
  have hcl : Subgroup.closure ({a, b} : Set Q) ≤ T := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe]
    rcases hx with hx | hx
    · rw [hx]; exact (hT a).mpr ha
    · rw [hx]; exact (hT b).mpr hb
  show ∀ g : Q, ∃ k : ℕ, g ^ 5 ^ k = 1
  intro g
  exact (hT g).mp (hcl (hgen g))

theorem h4_sylow_sup {K : Type*} [Group K] [Finite K] (M : Subgroup K) [M.Normal]
    (hM : IsPGroup 5 (K ⧸ M)) (P : Sylow 5 K) :
    (P : Subgroup K) ⊔ M = ⊤ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hM
  have hMidx : M.index = 5 ^ n := by
    rw [Subgroup.index_eq_card]; exact hn
  have h1 : ((P : Subgroup K) ⊔ M).index ∣ 5 ^ n := by
    rw [← hMidx]; exact Subgroup.index_dvd_of_le le_sup_right
  have h2 : ((P : Subgroup K) ⊔ M).index ∣ (P : Subgroup K).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have h3 : ¬ 5 ∣ (P : Subgroup K).index := Sylow.not_dvd_index P
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 h1
  have hm0 : m = 0 := by
    by_contra hne
    have h4 : 5 ^ m ∣ (P : Subgroup K).index := by
      rw [← hm]; exact h2
    exact h3 ((dvd_pow_self 5 hne).trans h4)
  apply Subgroup.index_eq_one.mp
  rw [hm, hm0, pow_zero]

theorem h4_lift_gen {X : Type*} [Group X] [Finite X] (N : Subgroup X) {x₁ x₂ : X}
    (hnorm : Subgroup.closure ({x₁, x₂} : Set X) ⊔ N ≤ Subgroup.normalizer (N : Set X))
    (hcomm : (x₁ * x₂)⁻¹ * (x₂ * x₁) ∈ N)
    (hx₁ : ∃ k : ℕ, x₁ ^ 5 ^ k = 1) (hx₂ : ∃ k : ℕ, x₂ ^ 5 ^ k = 1) :
    ∃ P : Subgroup X, IsPGroup 5 P ∧ P ≤ Subgroup.closure ({x₁, x₂} : Set X) ⊔ N ∧
      ∀ g ∈ Subgroup.closure ({x₁, x₂} : Set X) ⊔ N, ∃ p ∈ P, ∃ n ∈ N, g = p * n := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨E, hE⟩ : ∃ E : Subgroup X, E = Subgroup.closure ({x₁, x₂} : Set X) ⊔ N := ⟨_, rfl⟩
  rw [← hE] at hnorm ⊢
  have hNE : N ≤ E := by
    rw [hE]; exact le_sup_right
  have hx₁E : x₁ ∈ E := by
    rw [hE]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert _ _))
  have hx₂E : x₂ ∈ E := by
    rw [hE]
    exact Subgroup.mem_sup_left
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  haveI hM : (N.subgroupOf E).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  obtain ⟨k₁, hk₁⟩ := hx₁
  obtain ⟨k₂, hk₂⟩ := hx₂
  have hp₁ : (⟨x₁, hx₁E⟩ : ↥E) ^ 5 ^ k₁ = 1 := Subtype.ext (by simpa using hk₁)
  have hp₂ : (⟨x₂, hx₂E⟩ : ↥E) ^ 5 ^ k₂ = 1 := Subtype.ext (by simpa using hk₂)
  obtain ⟨a, ha_def⟩ : ∃ a : (↥E ⧸ N.subgroupOf E),
      a = QuotientGroup.mk' (N.subgroupOf E) (⟨x₁, hx₁E⟩ : ↥E) := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : (↥E ⧸ N.subgroupOf E),
      b = QuotientGroup.mk' (N.subgroupOf E) (⟨x₂, hx₂E⟩ : ↥E) := ⟨_, rfl⟩
  have ha5 : ∃ k : ℕ, a ^ 5 ^ k = 1 := ⟨k₁, by rw [ha_def, ← map_pow, hp₁, map_one]⟩
  have hb5 : ∃ k : ℕ, b ^ 5 ^ k = 1 := ⟨k₂, by rw [hb_def, ← map_pow, hp₂, map_one]⟩
  have hab : a * b = b * a := by
    rw [ha_def, hb_def, ← map_mul, ← map_mul]
    simp only [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hcomm
  obtain ⟨Lam, hLamdef⟩ : ∃ Lam : Subgroup X,
      Lam = ((Subgroup.closure ({a, b} : Set (↥E ⧸ N.subgroupOf E))).comap
        (QuotientGroup.mk' (N.subgroupOf E))).map E.subtype := ⟨_, rfl⟩
  have hmemLam : ∀ e : ↥E, QuotientGroup.mk' (N.subgroupOf E) e ∈
      Subgroup.closure ({a, b} : Set (↥E ⧸ N.subgroupOf E)) → (e : X) ∈ Lam := by
    intro e he
    rw [hLamdef]
    exact Subgroup.mem_map.mpr ⟨e, Subgroup.mem_comap.mpr he, rfl⟩
  have hLamE : E ≤ Lam := by
    rw [hE]
    apply sup_le
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe]
      rcases hx with hx | hx
      · rw [hx]
        refine hmemLam ⟨x₁, hx₁E⟩ ?_
        rw [← ha_def]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · rw [hx]
        refine hmemLam ⟨x₂, hx₂E⟩ ?_
        rw [← hb_def]
        exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · intro n hn
      have hnE : n ∈ E := hNE hn
      refine hmemLam ⟨n, hnE⟩ ?_
      have h1 : QuotientGroup.mk' (N.subgroupOf E) (⟨n, hnE⟩ : ↥E) = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr hn
      rw [h1]
      exact one_mem _
  have hgen : ∀ q : (↥E ⧸ N.subgroupOf E),
      q ∈ Subgroup.closure ({a, b} : Set (↥E ⧸ N.subgroupOf E)) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf E) q
    have hg : (g : X) ∈ Lam := hLamE g.2
    rw [hLamdef] at hg
    obtain ⟨e, he, hee⟩ := Subgroup.mem_map.mp hg
    have hge : e = g := Subtype.ext hee
    rw [← hge]
    exact Subgroup.mem_comap.mp he
  have hQ : IsPGroup 5 (↥E ⧸ N.subgroupOf E) := h4_isPGroup_of_gen ha5 hb5 hab hgen
  obtain ⟨P₀⟩ : Nonempty (Sylow 5 ↥E) := inferInstance
  have hsup : (P₀ : Subgroup ↥E) ⊔ N.subgroupOf E = ⊤ := h4_sylow_sup (N.subgroupOf E) hQ P₀
  refine ⟨(P₀ : Subgroup ↥E).map E.subtype, IsPGroup.map P₀.isPGroup' E.subtype, ?_, ?_⟩
  · rintro _ ⟨y, _, rfl⟩
    exact y.2
  · intro g hg
    have hmem : (⟨g, hg⟩ : ↥E) ∈ (P₀ : Subgroup ↥E) ⊔ N.subgroupOf E := by
      rw [hsup]; exact Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    refine ⟨(y : X), Subgroup.mem_map.mpr ⟨y, hy, rfl⟩, (z : X),
      Subgroup.mem_subgroupOf.mp hz, ?_⟩
    have h := congrArg Subtype.val hyz
    simp only [Subgroup.coe_mul] at h
    exact h.symm

theorem exists_five_lifts {θ H S K₁ K₂ : Subgroup G}
    (hθH : θ ≤ H) (hHθ : H ≤ normalizer (θ : Set G))
    (hK₁H : K₁ ≤ H) (hK₁S : K₁ ≤ normalizer (S : Set G))
    (hK₂H : K₂ ≤ H) (hK₂S : K₂ ≤ normalizer (S : Set G)) (hcomm : ⁅K₁, K₂⁆ ≤ θ)
    {x₁ x₂ : G} (hx₁ : x₁ ∈ K₁) (hx₂ : x₂ ∈ K₂) (hx₁5 : IsPGroup 5 (Subgroup.zpowers x₁))
    (hx₂5 : IsPGroup 5 (Subgroup.zpowers x₂)) :
    ∃ (P : Subgroup G) (y₁ y₂ n₁ n₂ : G), IsPGroup 5 P ∧ P ≤ normalizer (S : Set G) ∧ P ≤ H ∧
      y₁ ∈ P ∧ y₂ ∈ P ∧ n₁ ∈ θ ∧ n₁ ∈ normalizer (S : Set G) ∧ n₂ ∈ θ ∧
      n₂ ∈ normalizer (S : Set G) ∧ y₁ = x₁ * n₁ ∧ y₂ = x₂ * n₂ := by
  have hcommN : ∀ u ∈ K₁, ∀ v ∈ K₂, u * v * u⁻¹ * v⁻¹ ∈ θ ⊓ Subgroup.normalizer (S : Set G) := by
    intro u hu v hv
    refine Subgroup.mem_inf.mpr ⟨hcomm (commutator_mem_commutator hu hv), ?_⟩
    exact (Subgroup.normalizer (S : Set G)).mul_mem
      ((Subgroup.normalizer (S : Set G)).mul_mem
        ((Subgroup.normalizer (S : Set G)).mul_mem (hK₁S hu) (hK₂S hv))
        ((Subgroup.normalizer (S : Set G)).inv_mem (hK₁S hu)))
      ((Subgroup.normalizer (S : Set G)).inv_mem (hK₂S hv))
  have hcomm' : (x₁ * x₂)⁻¹ * (x₂ * x₁) ∈ θ ⊓ Subgroup.normalizer (S : Set G) := by
    have e : (x₁⁻¹ * x₂⁻¹ * x₁⁻¹⁻¹ * x₂⁻¹⁻¹)⁻¹ = (x₁ * x₂)⁻¹ * (x₂ * x₁) := by group
    rw [← e]
    exact (θ ⊓ Subgroup.normalizer (S : Set G)).inv_mem
      (hcommN x₁⁻¹ (K₁.inv_mem hx₁) x₂⁻¹ (K₂.inv_mem hx₂))
  have hnorm : Subgroup.closure ({x₁, x₂} : Set G) ⊔ (θ ⊓ Subgroup.normalizer (S : Set G)) ≤
      Subgroup.normalizer ((θ ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) := by
    apply sup_le
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe]
      rcases hx with hx | hx
      · rw [hx]; exact h4_mem_normalizer_inf (hHθ (hK₁H hx₁)) (hK₁S hx₁)
      · rw [hx]; exact h4_mem_normalizer_inf (hHθ (hK₂H hx₂)) (hK₂S hx₂)
    · exact Subgroup.le_normalizer
  obtain ⟨P, hP5, hPE, hcov⟩ := h4_lift_gen (θ ⊓ Subgroup.normalizer (S : Set G)) hnorm hcomm'
    (h4_pow_of_zpowers hx₁5) (h4_pow_of_zpowers hx₂5)
  have hEH : Subgroup.closure ({x₁, x₂} : Set G) ⊔ (θ ⊓ Subgroup.normalizer (S : Set G)) ≤ H := by
    apply sup_le
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe]
      rcases hx with hx | hx
      · rw [hx]; exact hK₁H hx₁
      · rw [hx]; exact hK₂H hx₂
    · exact inf_le_left.trans hθH
  have hES : Subgroup.closure ({x₁, x₂} : Set G) ⊔ (θ ⊓ Subgroup.normalizer (S : Set G)) ≤
      Subgroup.normalizer (S : Set G) := by
    apply sup_le
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe]
      rcases hx with hx | hx
      · rw [hx]; exact hK₁S hx₁
      · rw [hx]; exact hK₂S hx₂
    · exact inf_le_right
  have hPH : P ≤ H := hPE.trans hEH
  have hPS : P ≤ Subgroup.normalizer (S : Set G) := hPE.trans hES
  obtain ⟨p₁, hp₁, n₁, hn₁, e₁⟩ :=
    hcov x₁ (Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert _ _)))
  obtain ⟨p₂, hp₂, n₂, hn₂, e₂⟩ :=
    hcov x₂ (Subgroup.mem_sup_left
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  obtain ⟨hn₁θ, hn₁S⟩ := Subgroup.mem_inf.mp ((θ ⊓ Subgroup.normalizer (S : Set G)).inv_mem hn₁)
  obtain ⟨hn₂θ, hn₂S⟩ := Subgroup.mem_inf.mp ((θ ⊓ Subgroup.normalizer (S : Set G)).inv_mem hn₂)
  refine ⟨P, p₁, p₂, n₁⁻¹, n₂⁻¹, hP5, hPS, hPH, hp₁, hp₂, hn₁θ, hn₁S, hn₂θ, hn₂S, ?_, ?_⟩
  · rw [e₁, mul_inv_cancel_right]
  · rw [e₂, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec11

end

section

open CFSG Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11

variable {G : Type*} [Group G] [Finite G]

lemma h5_eq_one_of_fix {S P : Subgroup G} (ψ : P →* MulAut ↥S)
    (hψ : ∀ (g : ↥P) (s : ↥S), ((ψ g s : ↥S) : G) = (g : G) * (s : G) * (g : G)⁻¹)
    (a : ↥P) (h : ∀ s ∈ S, (a : G) * s * (a : G)⁻¹ = s) : ψ a = 1 := by
  refine MulEquiv.ext fun s => ?_
  rw [MulAut.one_apply]
  apply Subtype.ext
  rw [hψ]
  exact h (s : G) s.2

lemma h5_ne_one_of_exists {S P : Subgroup G} (ψ : P →* MulAut ↥S)
    (hψ : ∀ (g : ↥P) (s : ↥S), ((ψ g s : ↥S) : G) = (g : G) * (s : G) * (g : G)⁻¹)
    (a : ↥P) (h : ∃ s ∈ S, (a : G) * s * (a : G)⁻¹ ≠ s) : ψ a ≠ 1 := by
  rintro h1
  obtain ⟨s, hs, hne⟩ := h
  apply hne
  have h2 : ψ a ⟨s, hs⟩ = ⟨s, hs⟩ := by
    rw [h1, MulAut.one_apply]
  have h3 := congrArg Subtype.val h2
  rw [hψ] at h3
  exact h3

lemma h5_exists_of_ne_one {S P : Subgroup G} (ψ : P →* MulAut ↥S)
    (hψ : ∀ (g : ↥P) (s : ↥S), ((ψ g s : ↥S) : G) = (g : G) * (s : G) * (g : G)⁻¹)
    (a : ↥P) (h : ψ a ≠ 1) : ∃ s ∈ S, (a : G) * s * (a : G)⁻¹ ≠ s := by
  by_contra hcon
  push_neg at hcon
  exact h (h5_eq_one_of_fix ψ hψ a hcon)

lemma h5_comm_of_central {S P : Subgroup G} (ψ : P →* MulAut ↥S)
    (hψ : ∀ (g : ↥P) (s : ↥S), ((ψ g s : ↥S) : G) = (g : G) * (s : G) * (g : G)⁻¹)
    (a : ↥P) (hc : ∀ g : ↥P, ψ g * ψ a = ψ a * ψ g) :
    ∀ g ∈ P, ∀ s ∈ S, (a : G) * (g * s * g⁻¹) * (a : G)⁻¹ = g * ((a : G) * s * (a : G)⁻¹) * g⁻¹ := by
  intro g hg s hs
  have h1 := DFunLike.congr_fun (hc ⟨g, hg⟩) ⟨s, hs⟩
  rw [MulAut.mul_apply, MulAut.mul_apply] at h1
  have h2 := congrArg Subtype.val h1
  simp only [hψ] at h2
  exact h2.symm

lemma h5_eq_zpow_of_act {S P : Subgroup G} (ψ : P →* MulAut ↥S)
    (hψ : ∀ (g : ↥P) (s : ↥S), ((ψ g s : ↥S) : G) = (g : G) * (s : G) * (g : G)⁻¹)
    (a b : ↥P) (j : ℤ)
    (h : ∀ s ∈ S, (b : G) * s * (b : G)⁻¹ = (a : G) ^ j * s * ((a : G) ^ j)⁻¹) :
    ψ b = ψ a ^ j := by
  have hpow : ψ (a ^ j) = ψ a ^ j := map_zpow ψ a j
  rw [← hpow]
  refine MulEquiv.ext fun s => ?_
  apply Subtype.ext
  rw [hψ, hψ, Subgroup.coe_zpow]
  exact h (s : G) s.2

lemma h5_core {S P : Subgroup G} (hP5 : IsPGroup 5 P) (ψ : P →* MulAut ↥S)
    (hψ : ∀ (g : ↥P) (s : ↥S), ((ψ g s : ↥S) : G) = (g : G) * (s : G) * (g : G)⁻¹)
    (hV : ∀ a ∈ P, (∀ g ∈ P, ∀ s ∈ S, a * (g * s * g⁻¹) * a⁻¹ = g * (a * s * a⁻¹) * g⁻¹) →
      (∃ s ∈ S, a * s * a⁻¹ ≠ s) → ∀ b ∈ P, ∃ j : ℤ, ∀ s ∈ S, b * s * b⁻¹ = a ^ j * s * (a ^ j)⁻¹)
    {y₁ y₂ : G} (hy₁ : y₁ ∈ P) (hy₂ : y₂ ∈ P) (hnt : ∃ s ∈ S, y₁ * s * y₁⁻¹ ≠ s) :
    ∃ c : ℤ, ∀ s ∈ S, y₂ * s * y₂⁻¹ = y₁ ^ c * s * (y₁ ^ c)⁻¹ := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hy1ne : ψ ⟨y₁, hy₁⟩ ≠ 1 := h5_ne_one_of_exists ψ hψ ⟨y₁, hy₁⟩ hnt
  have hmem1 : ψ ⟨y₁, hy₁⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  haveI : Finite ψ.range :=
    Finite.of_surjective ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
  haveI : Nontrivial ψ.range :=
    nontrivial_of_ne ⟨ψ ⟨y₁, hy₁⟩, hmem1⟩ 1 (fun h => hy1ne (congrArg Subtype.val h))
  have hH5 : IsPGroup 5 ψ.range :=
    hP5.of_surjective ψ.rangeRestrict (MonoidHom.rangeRestrict_surjective ψ)
  haveI : Nontrivial (Subgroup.center ψ.range) := IsPGroup.center_nontrivial hH5
  have hZ5 : IsPGroup 5 (Subgroup.center ψ.range) := hH5.to_subgroup _
  have hne1 : Nat.card (Subgroup.center ψ.range) ≠ 1 := Finite.one_lt_card.ne'
  have hcard : 5 ∣ Nat.card (Subgroup.center ψ.range) := hZ5.card_eq_or_dvd.resolve_left hne1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 hcard
  obtain ⟨z, hzr, hzc, hzo⟩ : ∃ z : MulAut ↥S, z ∈ ψ.range ∧ (∀ g : ↥P, ψ g * z = z * ψ g) ∧
      orderOf z = 5 := by
    refine ⟨((x : ↥ψ.range) : MulAut ↥S), (x : ↥ψ.range).2, fun g => ?_, ?_⟩
    · have hc := Subgroup.mem_center_iff.mp x.2 ⟨ψ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩
      exact congrArg Subtype.val hc
    · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      exact hx
  obtain ⟨a', rfl⟩ := MonoidHom.mem_range.mp hzr
  have hw1 : ψ a' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    norm_num at hzo
  have hw5 : ψ a' ^ (5 : ℤ) = 1 := by
    rw [zpow_ofNat]
    have := pow_orderOf_eq_one (ψ a')
    rwa [hzo] at this
  have hnt' : ∃ s ∈ S, (a' : G) * s * (a' : G)⁻¹ ≠ s := h5_exists_of_ne_one ψ hψ a' hw1
  have hcomm := h5_comm_of_central ψ hψ a' hzc
  have hb := hV (a' : G) a'.2 hcomm hnt'
  obtain ⟨j₁, hj₁⟩ := hb y₁ hy₁
  obtain ⟨j₂, hj₂⟩ := hb y₂ hy₂
  have e1 : ψ ⟨y₁, hy₁⟩ = ψ a' ^ j₁ := h5_eq_zpow_of_act ψ hψ a' ⟨y₁, hy₁⟩ j₁ hj₁
  have e2 : ψ ⟨y₂, hy₂⟩ = ψ a' ^ j₂ := h5_eq_zpow_of_act ψ hψ a' ⟨y₂, hy₂⟩ j₂ hj₂
  have hndvd : ¬ (5 : ℤ) ∣ j₁ := by
    rintro ⟨t, ht⟩
    apply hy1ne
    rw [e1, ht, zpow_mul, hw5, one_zpow]
  have hp5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp5.irreducible).mpr hndvd
  have hexp : j₁ * (j₂ * v) = j₂ + -(j₂ * u) * 5 := by linear_combination j₂ * huv
  have key : ψ ⟨y₂, hy₂⟩ = ψ ⟨y₁, hy₁⟩ ^ (j₂ * v) := by
    rw [e1, e2, ← zpow_mul, hexp, zpow_add, zpow_mul', hw5, one_zpow, mul_one]
  refine ⟨j₂ * v, fun s hs => ?_⟩
  have hkey : ψ ⟨y₂, hy₂⟩ = ψ ((⟨y₁, hy₁⟩ : ↥P) ^ (j₂ * v)) :=
    key.trans (map_zpow ψ _ _).symm
  have h2 := congrArg Subtype.val (DFunLike.congr_fun hkey ⟨s, hs⟩)
  rw [hψ, hψ] at h2
  exact h2

theorem exists_zpow_action {S P : Subgroup G} (hP5 : IsPGroup 5 P) (hPS : P ≤ normalizer (S : Set G))
    (hV : ∀ a ∈ P, (∀ g ∈ P, ∀ s ∈ S, a * (g * s * g⁻¹) * a⁻¹ = g * (a * s * a⁻¹) * g⁻¹) →
      (∃ s ∈ S, a * s * a⁻¹ ≠ s) → ∀ b ∈ P, ∃ j : ℤ, ∀ s ∈ S, b * s * b⁻¹ = a ^ j * s * (a ^ j)⁻¹)
    {y₁ y₂ : G} (hy₁ : y₁ ∈ P) (hy₂ : y₂ ∈ P) (hnt : ∃ s ∈ S, y₁ * s * y₁⁻¹ ≠ s) :
    ∃ c : ℤ, ∀ s ∈ S, y₂ * s * y₂⁻¹ = y₁ ^ c * s * (y₁ ^ c)⁻¹ := by
  exact h5_core hP5 ((Subgroup.normalizerMonoidHom S).comp (Subgroup.inclusion hPS))
    (fun _ _ => rfl) hV hy₁ hy₂ hnt

end CFSG.RankThree.PartTwo.Sec11

end
