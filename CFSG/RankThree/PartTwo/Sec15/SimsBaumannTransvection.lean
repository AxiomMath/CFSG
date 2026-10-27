module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec15.SimsBaumann

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS

variable {G : Type*} [Group G] [Finite G]

private theorem sbtvprod_iterate_six {α : Type*} {S : Set α} (hS : S.Finite) (hcard : S.ncard ≤ 3)
    {f : α → α} (hmaps : Set.MapsTo f S S) (hinj : Set.InjOn f S) {s : α} (hs : s ∈ S) :
    f^[6] s = s := by
  haveI : Finite S := hS.to_subtype
  let g : S → S := fun t => ⟨f t, hmaps t.2⟩
  have hg : Function.Injective g := fun a b h =>
    Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val h))
  let σ : Equiv.Perm S := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)
  have hpow : ∀ (n : ℕ) (t : S), (((σ ^ n) t : S) : α) = f^[n] (t : α) := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      calc (((σ ^ (n + 1)) t : S) : α) = (((σ ((σ ^ n) t)) : S) : α) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
        _ = f (((σ ^ n) t : S) : α) := rfl
        _ = f (f^[n] (t : α)) := by rw [ih]
        _ = f^[n + 1] (t : α) := (Function.iterate_succ_apply' f n _).symm
  have h6 : σ ^ 6 = 1 := by
    have h1 : σ ^ Nat.card (Equiv.Perm S) = 1 := pow_card_eq_one'
    rw [Nat.card_perm] at h1
    have hle : Nat.card S ≤ 3 := by rw [Nat.card_coe_set_eq]; exact hcard
    obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial hle
    have h3 : Nat.factorial 3 = 6 := rfl
    rw [h3] at hm
    rw [hm, pow_mul, h1, one_pow]
  have h := hpow 6 ⟨s, hs⟩
  rw [h6] at h
  exact h.symm

omit [Finite G] in
private theorem sbtvprod_exists_commHom {V : Subgroup G} (hV : IsMulCommutative V) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    ∃ N : V →* G, ∀ v : V, N v = g * (v : G) * g⁻¹ * (v : G)⁻¹ := by
  haveI := hV
  have hmem : ∀ w : G, w ∈ V → g * w * g⁻¹ ∈ V := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hg w).mp hw
  refine ⟨MonoidHom.mk' (fun v : V => g * (v : G) * g⁻¹ * (v : G)⁻¹) ?_, fun v => rfl⟩
  intro a b
  have hd : g * (b : G) * g⁻¹ * (b : G)⁻¹ ∈ V := V.mul_mem (hmem _ b.2) (V.inv_mem b.2)
  have hc : (a : G)⁻¹ * (g * (b : G) * g⁻¹ * (b : G)⁻¹) =
      (g * (b : G) * g⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ := setLike_mul_comm (V.inv_mem a.2) hd
  show g * ((a : G) * (b : G)) * g⁻¹ * ((a : G) * (b : G))⁻¹ =
    (g * (a : G) * g⁻¹ * (a : G)⁻¹) * (g * (b : G) * g⁻¹ * (b : G)⁻¹)
  calc g * ((a : G) * (b : G)) * g⁻¹ * ((a : G) * (b : G))⁻¹
      = (g * (a : G) * g⁻¹) * ((g * (b : G) * g⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
    _ = (g * (a : G) * g⁻¹) * ((a : G)⁻¹ * (g * (b : G) * g⁻¹ * (b : G)⁻¹)) := by rw [hc]
    _ = (g * (a : G) * g⁻¹ * (a : G)⁻¹) * (g * (b : G) * g⁻¹ * (b : G)⁻¹) := by group

private theorem sbtvprod_card_range_le {V : Subgroup G} {x y : G} (N : V →* G)
    (hN : ∀ v : V, N v = x * y * (v : G) * (x * y)⁻¹ * (v : G)⁻¹)
    (hx : (V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex V ≤ 2)
    (hy : (V ⊓ Subgroup.centralizer ({y} : Set G)).relIndex V ≤ 2) :
    Nat.card N.range ≤ 4 := by
  have h1 : ((V ⊓ Subgroup.centralizer ({x} : Set G)) ⊓
      (V ⊓ Subgroup.centralizer ({y} : Set G))).relIndex V ≤ 4 :=
    calc _ ≤ (V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex V *
          (V ⊓ Subgroup.centralizer ({y} : Set G)).relIndex V := Subgroup.relIndex_inf_le
      _ ≤ 2 * 2 := Nat.mul_le_mul hx hy
  have h2 : ((V ⊓ Subgroup.centralizer ({x} : Set G)) ⊓
      (V ⊓ Subgroup.centralizer ({y} : Set G))).relIndex V ≠ 0 := by
    intro h0
    have h3 := Subgroup.relIndex_dvd_card ((V ⊓ Subgroup.centralizer ({x} : Set G)) ⊓
      (V ⊓ Subgroup.centralizer ({y} : Set G))) V
    rw [h0, zero_dvd_iff] at h3
    exact Nat.card_pos.ne' h3
  have h3 : ((V ⊓ Subgroup.centralizer ({x} : Set G)) ⊓
      (V ⊓ Subgroup.centralizer ({y} : Set G))).subgroupOf V ≤ N.ker := by
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv
    have hvx : (v : G) * x = x * (v : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv).1).2
    have hvy : (v : G) * y = y * (v : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hv).2).2
    have hcomm : x * y * (v : G) = (v : G) * (x * y) := by
      rw [mul_assoc, ← hvy, ← mul_assoc, ← hvx, mul_assoc]
    rw [MonoidHom.mem_ker, hN, hcomm, mul_inv_cancel_right, mul_inv_cancel]
  have h4 : N.ker.index ∣ ((V ⊓ Subgroup.centralizer ({x} : Set G)) ⊓
      (V ⊓ Subgroup.centralizer ({y} : Set G))).relIndex V := Subgroup.index_dvd_of_le h3
  rw [← Subgroup.index_ker]
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h4).trans h1

private theorem sbtvprod_core {V U : Subgroup G} {g : G} (hUV : U ≤ V)
    (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hU4 : Nat.card U ≤ 4)
    (hgV : ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hcomm : ∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ U) :
    ∀ v ∈ V, g ^ 12 * v = v * g ^ 12 := by
  have hit : ∀ k : ℕ, ∀ v ∈ V,
      g ^ k * v * (g ^ k)⁻¹ ∈ V ∧ g ^ k * v * (g ^ k)⁻¹ * v⁻¹ ∈ U := by
    intro k
    induction k with
    | zero => intro v hv; simp [hv]
    | succ k ih =>
      intro v hv
      obtain ⟨hw, hwU⟩ := ih v hv
      have e : g ^ (k + 1) * v * (g ^ (k + 1))⁻¹ = g * (g ^ k * v * (g ^ k)⁻¹) * g⁻¹ := by
        rw [pow_succ']; group
      refine ⟨by rw [e]; exact hgV _ hw, ?_⟩
      have e2 : g ^ (k + 1) * v * (g ^ (k + 1))⁻¹ * v⁻¹ =
          (g * (g ^ k * v * (g ^ k)⁻¹) * g⁻¹ * (g ^ k * v * (g ^ k)⁻¹)⁻¹) *
            (g ^ k * v * (g ^ k)⁻¹ * v⁻¹) := by
        rw [e]; group
      rw [e2]
      exact U.mul_mem (hcomm _ hw) hwU
  have hUc : ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro u hu
    simpa using U.mul_mem (hcomm u (hUV hu)) hu
  have hU6 : ∀ u ∈ U, g ^ 6 * u * (g ^ 6)⁻¹ = u := by
    intro u hu
    by_cases hu1 : u = 1
    · subst hu1; simp
    · have hiter : ∀ (n : ℕ) (w : G),
          (fun w : G => g * w * g⁻¹)^[n] w = g ^ n * w * (g ^ n)⁻¹ := by
        intro n
        induction n with
        | zero => intro w; simp
        | succ n ih =>
          intro w
          rw [Function.iterate_succ_apply', ih, pow_succ']
          group
      have hS : ((U : Set G) \ {1}).ncard ≤ 3 := by
        rw [Set.ncard_sdiff_singleton_of_mem (by exact U.one_mem)]
        have h : (U : Set G).ncard = Nat.card U := (Nat.card_coe_set_eq (U : Set G)).symm
        omega
      have hmaps : Set.MapsTo (fun w : G => g * w * g⁻¹) ((U : Set G) \ {1})
          ((U : Set G) \ {1}) := by
        rintro w ⟨hwU, hw1⟩
        refine ⟨hUc w hwU, ?_⟩
        intro h
        have h' : g * w * g⁻¹ = 1 := Set.mem_singleton_iff.mp h
        exact hw1 (Set.mem_singleton_iff.mpr (conj_eq_one_iff.mp h'))
      have hinj : Set.InjOn (fun w : G => g * w * g⁻¹) ((U : Set G) \ {1}) := by
        intro a _ b _ h
        simpa using h
      have := sbtvprod_iterate_six (Set.toFinite _) hS hmaps hinj
        (show u ∈ (U : Set G) \ {1} from ⟨hu, hu1⟩)
      rwa [hiter] at this
  intro v hv
  have hu₀ := (hit 6 v hv).2
  generalize hu : g ^ 6 * v * (g ^ 6)⁻¹ * v⁻¹ = u₀ at hu₀
  have E1 : g ^ 6 * v * (g ^ 6)⁻¹ = u₀ * v := by rw [← hu]; group
  have E2 : g ^ 6 * u₀ * (g ^ 6)⁻¹ = u₀ := hU6 u₀ hu₀
  have E3 : u₀ * u₀ = 1 := by
    have := hV2 u₀ (hUV hu₀)
    rwa [pow_two] at this
  have key : g ^ 6 * g ^ 6 * v * (g ^ 6)⁻¹ * (g ^ 6)⁻¹ = v := by
    calc g ^ 6 * g ^ 6 * v * (g ^ 6)⁻¹ * (g ^ 6)⁻¹
        = g ^ 6 * (g ^ 6 * v * (g ^ 6)⁻¹) * (g ^ 6)⁻¹ := by group
      _ = g ^ 6 * (u₀ * v) * (g ^ 6)⁻¹ := by rw [E1]
      _ = (g ^ 6 * u₀ * (g ^ 6)⁻¹) * (g ^ 6 * v * (g ^ 6)⁻¹) := by group
      _ = u₀ * (u₀ * v) := by rw [E2, E1]
      _ = (u₀ * u₀) * v := (mul_assoc _ _ _).symm
      _ = v := by rw [E3, one_mul]
  calc g ^ 12 * v = (g ^ 6 * g ^ 6 * v * (g ^ 6)⁻¹ * (g ^ 6)⁻¹) * (g ^ 6 * g ^ 6) := by
        rw [← pow_add]; group
    _ = v * g ^ 12 := by rw [key, ← pow_add]

theorem pow_twelve_mem_centralizer {V : Subgroup G} (hV : CFSG.Assembly.IsElemAbelian 2 V)
    {x y : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hx : (V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex V ≤ 2)
    (hy : (V ⊓ Subgroup.centralizer ({y} : Set G)).relIndex V ≤ 2) :
    (x * y) ^ 12 ∈ Subgroup.centralizer (V : Set G) := by
  have hgV : x * y ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hxV hyV
  obtain ⟨N, hN⟩ := sbtvprod_exists_commHom hV.1 hgV
  have hmem : ∀ w : G, w ∈ V → x * y * w * (x * y)⁻¹ ∈ V := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hgV w).mp hw
  have hUV : N.range ≤ V := by
    rintro _ ⟨v, rfl⟩
    rw [hN]
    exact V.mul_mem (hmem _ v.2) (V.inv_mem v.2)
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  exact (sbtvprod_core hUV hV.2 (sbtvprod_card_range_le N hN hx hy) hmem
    (fun w hw => ⟨⟨w, hw⟩, hN ⟨w, hw⟩⟩) v hv).symm

end CFSG.RankThree.PartTwo.Sec15.SimsBaumann
