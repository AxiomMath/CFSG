module

public import CFSG.Quasithin.EmptyFaithful.S152N2Grp
public import CFSG.Quasithin.EmptyFaithful.S152N2Fix

public section

namespace CFSG.Quasithin

namespace S152N2

open CFSG.Open CFSG.QuasithinUnique

abbrev D33 := DihedralGroup 3 × DihedralGroup 3

@[expose] def A33 : Subgroup D33 where
  carrier := {x | x.1 ^ 3 = 1 ∧ x.2 ^ 3 = 1}
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    revert a b
    decide
  inv_mem' := by
    intro a ha
    revert a
    decide

instance instDecidableMemA33 : DecidablePred (· ∈ A33) := fun x =>
  inferInstanceAs (Decidable (x.1 ^ 3 = 1 ∧ x.2 ^ 3 = 1))

theorem A33_card : Nat.card A33 = 9 := by
  have : Nat.card A33 = Fintype.card A33 := Nat.card_eq_fintype_card
  rw [this]
  decide

theorem A33_normal : A33.Normal := by
  constructor
  intro n hn g
  revert n g
  decide

theorem A33_sq : ∀ x : D33, x ^ 2 ∈ A33 := by decide

theorem A33_comm : ∀ a ∈ A33, ∀ b ∈ A33, a * b = b * a := by decide

theorem A33_sc : ∀ x : D33, (∀ n ∈ A33, x * n = n * x) → x ∈ A33 := by decide

variable {Γ : Type*} [Group Γ]

theorem shapeConcl_of_s3s3 [Finite Γ] {X Tb : Subgroup Γ} (hTb : IsSylowTwoOf Tb X)
    (e : ↥X ≃* D33) (Bs : Set (Subgroup Γ))
    (hBs : ∀ B ∈ Bs, B ≤ Tb ∧ Nat.card B = 2 ∧
      ∀ y ∈ X, y ^ 3 = 1 → (∀ b ∈ B, b * y = y * b) → y = 1) : ShapeConcl X Tb Bs := by
  set N' : Subgroup X := A33.comap (e : ↥X →* D33) with hN'
  set N : Subgroup Γ := N'.map X.subtype with hN
  have hNX : N ≤ X := Subgroup.map_subtype_le _
  have hNsub : N.subgroupOf X = N' := Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  have hnorm : (N.subgroupOf X).Normal := by
    rw [hNsub]; exact A33_normal.comap _
  have hcardN' : Nat.card N' = 9 := by
    rw [hN', Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective e.symm.injective,
      A33_card]
  have hcardN : Nat.card N = 9 := by
    rw [hN, Subgroup.card_map_of_injective X.subtype_injective, hcardN']
  have hmemN : ∀ x : Γ, x ∈ N ↔ ∃ hx : x ∈ X, e ⟨x, hx⟩ ∈ A33 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) ∈ N := by
    intro x hx
    refine ⟨1, (hmemN _).mpr ⟨X.pow_mem hx _, ?_⟩⟩
    have : e ⟨x ^ 2 ^ 1, X.pow_mem hx _⟩ = (e ⟨x, hx⟩) ^ 2 := by
      rw [← map_pow]; rfl
    rw [this]
    exact A33_sq _
  have hON : oddCoreIn X = N :=
    oddCoreIn_eq_of_normal hNX hnorm (by rw [hcardN]; exact ⟨4, rfl⟩) hpow
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    obtain ⟨hax, ha'⟩ := (hmemN a).mp ha
    obtain ⟨hbx, hb'⟩ := (hmemN b).mp hb
    have := A33_comm _ ha' _ hb'
    rw [← map_mul, ← map_mul] at this
    have h2 := e.injective this
    exact congrArg Subtype.val h2
  have hSC : ∀ x ∈ X, (∀ n ∈ N, x * n = n * x) → x ∈ N := by
    intro x hx hxc
    refine (hmemN x).mpr ⟨hx, A33_sc _ fun m hm => ?_⟩
    have hmem : (e.symm m : Γ) ∈ N := (hmemN _).mpr ⟨(e.symm m).2, by simpa using hm⟩
    have := hxc _ hmem
    have h2 : (⟨x, hx⟩ : X) * e.symm m = e.symm m * ⟨x, hx⟩ := Subtype.ext this
    have h3 := congrArg e h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3
  have hexp : ∀ n ∈ N, n ^ 3 = 1 := by
    intro n hn
    obtain ⟨hnx, hn'⟩ := (hmemN n).mp hn
    have h1 : (e ⟨n, hnx⟩) ^ 3 = 1 := by
      obtain ⟨h1, h2⟩ := hn'
      exact Prod.ext h1 h2
    rw [← map_pow] at h1
    have := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val this
  refine shapeConcl_of_oddCore hTb hON hcomm hSC Bs fun B hB => ?_
  obtain ⟨hBT, hBc, hstar⟩ := hBs B hB
  refine ⟨hBT, hBc, fun b hbB hb1 n hn => ?_⟩
  obtain ⟨b₀, -, hb₀2, hBeq⟩ := exists_zpowers_eq_of_card_two hBc
  have hbeq : b = b₀ := by
    rw [hBeq] at hbB
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hbB
    rcases zpow_eq_one_or_self' hb₀2 k with h | h
    · exact absurd h hb1
    · exact h
  subst hbeq
  have hbX : b ∈ X := hTb.1 (hBT hbB)
  have hbN : b ∈ Subgroup.normalizer (N : Set Γ) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mp hnorm) hbX
  have hfix : N ⊓ Subgroup.centralizer ({b} : Set Γ) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyN, hyC⟩ := hy
    have hyb : b * y = y * b := (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
    have hy3 : y ^ 3 = 1 := hexp y hyN
    have hcomB : ∀ b' ∈ B, b' * y = y * b' := by
      intro b' hb'
      rw [hBeq] at hb'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
      exact ((Commute.zpow_left (show Commute b y from hyb) k)).eq
    exact hstar y (hNX hyN) hy3 hcomB
  have hb2 : b ^ 2 = 1 := by rw [sq]; exact hb₀2
  have := (inverts_and_commute_of_inf_centralizer_eq_bot hb2 hbN hfix).1 n hn
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb₀2
  rw [hbinv] at this ⊢
  exact this

theorem exists_gen_of_card_prime {N : Subgroup Γ} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card N = p) : ∃ x₀ ∈ N, x₀ ≠ 1 ∧ N = Subgroup.zpowers x₀ := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card N := by rw [hcard]
  have : Finite N := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hord : orderOf (c : Γ) = p := by rw [Subgroup.orderOf_coe]; exact hc
  refine ⟨c, c.2, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne hord
  · symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact (Subgroup.zpowers_le).mpr c.2
    · rw [Nat.card_zpowers, hord, hcard]

variable {V : Type*} [CommGroup V]

theorem five_small [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    {X X₀ : Subgroup (MulAut V)} (hX₀X : X₀ ≤ X)
    (hXn : X ≤ Subgroup.normalizer (X₀ : Set (MulAut V)))
    (h10 : Nat.card X₀ = 10) (hnc : ∃ a ∈ X₀, ∃ b ∈ X₀, a * b ≠ b * a)
    (hF : ∀ K : Subgroup (MulAut V), K ≤ X → X ≤ Subgroup.normalizer (K : Set (MulAut V)) →
      (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) → K ≤ X₀) :
    ∃ N : Subgroup (MulAut V), N ≤ X₀ ∧ (N.subgroupOf X).Normal ∧ Nat.card N = 5 ∧
      (∀ x ∈ X, (∀ n ∈ N, x * n = n * x) → x ∈ N) ∧ Nat.card X ∣ 20 := by
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) (fun f g h => DFunLike.coe_injective h)
  have hp5 : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp5⟩
  obtain ⟨N, hNX₀, -, hcardN, -, hpow₀⟩ :=
    exists_normal_prime_of_card_two_mul (X := X₀) hp5 (by rw [h10]) hnc
  have hNX : N ≤ X := hNX₀.trans hX₀X
  have hN5 : ∀ n ∈ N, n ^ 5 = 1 := by
    intro n hn
    have h1 : (⟨n, hn⟩ : N) ^ (Nat.card N) = 1 := pow_card_eq_one'
    rw [hcardN] at h1
    exact congrArg Subtype.val h1
  have hconjN : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    have hx₀ : g * n * g⁻¹ ∈ X₀ := (Subgroup.mem_normalizer_iff.mp (hXn hg) n).mp (hNX₀ hn)
    have hx5 : (g * n * g⁻¹) ^ 5 = 1 := by
      rw [conj_pow, hN5 n hn]; simp
    have hsq : (g * n * g⁻¹) ^ 2 ∈ N := hpow₀ _ hx₀
    set x := g * n * g⁻¹ with hx
    have h4 : x ^ 4 * x = 1 := by rw [← pow_succ]; exact hx5
    have hinv : (x ^ 4)⁻¹ = x := inv_eq_of_mul_eq_one_right h4
    have hxx : x = ((x ^ 2)⁻¹) ^ 2 := by
      calc x = (x ^ 4)⁻¹ := hinv.symm
        _ = ((x ^ 2)⁻¹) ^ 2 := by rw [inv_pow, ← pow_mul]
    rw [hxx]
    exact N.pow_mem (N.inv_mem hsq) 2
  have hconjN' : ∀ g ∈ X, ∀ n, n ∈ N ↔ g * n * g⁻¹ ∈ N := by
    intro g hg n
    constructor
    · exact hconjN g hg n
    · intro h
      have := hconjN g⁻¹ (X.inv_mem hg) _ h
      have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
      rwa [e] at this
  have hnormN : (N.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNX]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    exact hconjN' g hg
  obtain ⟨x₀, hx₀N, hx₀1, hNeq⟩ := exists_gen_of_card_prime hp5 hcardN
  have hx₀5 : x₀ ^ 5 = 1 := hN5 x₀ hx₀N
  have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    rw [hNeq] at ha hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self x₀ i j).eq
  set C : Subgroup (MulAut V) := X ⊓ Subgroup.centralizer (N : Set (MulAut V)) with hCdef
  have hCmem : ∀ c ∈ C, c ∈ X ∧ ∀ n ∈ N, c * n = n * c := by
    intro c hc
    refine ⟨hc.1, fun n hn => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hc.2 n hn).symm
  have hmemC : ∀ c ∈ X, (∀ n ∈ N, c * n = n * c) → c ∈ C := fun c hc h =>
    ⟨hc, Subgroup.mem_centralizer_iff.mpr fun n hn => (h n hn).symm⟩
  have hNC : N ≤ C := fun n hn => hmemC n (hNX hn) (fun m hm => hNcomm n hn m hm)
  have hCx₀ : ∀ c ∈ C, c * x₀ = x₀ * c := fun c hc => (hCmem c hc).2 x₀ hx₀N
  have hC15 : Nat.card C ≤ 15 := card_le_fifteen hcard hx₀5 hx₀1 hCx₀
  have hC5dvd : 5 ∣ Nat.card C := by
    have := Subgroup.card_dvd_of_le hNC
    rwa [hcardN] at this
  have hCodd : ¬ 2 ∣ Nat.card C := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hord : orderOf (c : MulAut V) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
    have hcc : (c : MulAut V) * c = 1 := by
      have := pow_orderOf_eq_one (c : MulAut V)
      rwa [hord, sq] at this
    obtain ⟨v, hv1, hcv⟩ := exists_fixed_of_involution hV2 hcard hcc
    have := eq_one_of_fixes_orbit hcard hx₀5 hx₀1 (hCx₀ c c.2) hv1 hcv
    rw [this, orderOf_one] at hord
    omega
  have hC515 : Nat.card C = 5 ∨ Nat.card C = 15 := by omega
  have hCN : C = N := by
    rcases hC515 with h5 | h15
    · exact (Subgroup.eq_of_le_of_card_ge hNC (by rw [h5, hcardN])).symm
    · exfalso
      have key : ∀ g ∈ X, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
        intro g hg c hc
        refine ⟨X.mul_mem (X.mul_mem hg (hCmem c hc).1) (X.inv_mem hg),
          Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
        have hm : g⁻¹ * n * g ∈ N := by
          have := hconjN g⁻¹ (X.inv_mem hg) n hn
          simpa using this
        have h1 := (hCmem c hc).2 _ hm
        calc n * (g * c * g⁻¹) = g * ((g⁻¹ * n * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * n * g)) * g⁻¹ := by rw [h1]
          _ = (g * c * g⁻¹) * n := by group
      have hXC : X ≤ Subgroup.normalizer (C : Set (MulAut V)) := by
        intro g hg
        rw [Subgroup.mem_normalizer_iff]
        intro c
        constructor
        · exact key g hg c
        · intro h
          have := key g⁻¹ (X.inv_mem hg) _ h
          have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
          rwa [e] at this
      have hCabel : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
        have h3 : 3 ∣ Nat.card C := by rw [h15]; norm_num
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
        have hordy : orderOf (y : MulAut V) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
        have hxy : (x₀ : MulAut V) * y = y * x₀ := (hCx₀ y y.2).symm
        set K : Subgroup (MulAut V) := Subgroup.closure {x₀, (y : MulAut V)} with hK
        have hKC : K ≤ C := by
          rw [hK, Subgroup.closure_le]
          intro z hz
          rcases hz with rfl | hz
          · exact hNC hx₀N
          · rw [Set.mem_singleton_iff.mp hz]; exact y.2
        have hx₀ord : orderOf x₀ = 5 := orderOf_eq_prime hx₀5 hx₀1
        have h5K : 5 ∣ Nat.card K := by
          have hx₀K : x₀ ∈ K := Subgroup.subset_closure (by simp)
          have := orderOf_dvd_natCard (⟨x₀, hx₀K⟩ : K)
          rwa [Subgroup.orderOf_mk, hx₀ord] at this
        have h3K : 3 ∣ Nat.card K := by
          have hyK : (y : MulAut V) ∈ K := Subgroup.subset_closure (by simp)
          have := orderOf_dvd_natCard (⟨(y : MulAut V), hyK⟩ : K)
          rwa [Subgroup.orderOf_mk, hordy] at this
        have hKle : Nat.card K ≤ Nat.card C := Subgroup.card_le_of_le hKC
        have hpos : 0 < Nat.card K := Nat.card_pos
        have hKcard : Nat.card K = 15 := by omega
        have hKeq : K = C := Subgroup.eq_of_le_of_card_ge hKC (by rw [h15, hKcard])
        have hpair : ({x₀, (y : MulAut V)} : Set (MulAut V)).Pairwise Commute := by
          intro a ha b hb _
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact Commute.refl _
          · rw [Set.mem_singleton_iff.mp hb]; exact hxy
          · rw [Set.mem_singleton_iff.mp ha]; exact hxy.symm
          · rw [Set.mem_singleton_iff.mp ha, Set.mem_singleton_iff.mp hb]
        have : IsMulCommutative K := Subgroup.isMulCommutative_closure hpair
        intro a ha b hb
        rw [← hKeq] at ha hb
        exact setLike_mul_comm (s := K) ha hb
      have hCX₀ := hF C inf_le_left hXC hCabel
      have := Subgroup.card_dvd_of_le hCX₀
      rw [h15, h10] at this
      omega
  refine ⟨N, hNX₀, hnormN, hcardN, ?_, ?_⟩
  · intro x hx hxc
    have : x ∈ C := hmemC x hx hxc
    rw [hCN] at this
    exact this
  · have hXN : X ≤ Subgroup.normalizer (N : Set (MulAut V)) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      exact hconjN' g hg
    have hcycN : IsCyclic N := isCyclic_of_prime_card hcardN
    let φ : X →* MulAut N := (N.normalizerMonoidHom).comp (Subgroup.inclusion hXN)
    have hφ : ∀ (g : X) (n : N), ((φ g n : N) : MulAut V) = g * n * (g : MulAut V)⁻¹ := fun g n =>
      Subgroup.normalizerMonoidHom_apply_apply_coe N (Subgroup.inclusion hXN g) n
    have hker : φ.ker = N.subgroupOf X := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have hg : (g : MulAut V) ∈ C := by
          refine hmemC g g.2 fun n hn => ?_
          have h1 : ((φ g ⟨n, hn⟩ : N) : MulAut V) = n := by rw [h]; rfl
          rw [hφ] at h1
          calc (g : MulAut V) * n = (g * n * (g : MulAut V)⁻¹) * g := by group
            _ = n * g := by rw [h1]
        rw [hCN] at hg
        exact hg
      · intro h
        apply MulEquiv.ext
        rintro ⟨n, hn⟩
        apply Subtype.ext
        show ((φ g ⟨n, hn⟩ : N) : MulAut V) = n
        rw [hφ]
        have h3 : (g : MulAut V) ∈ C := by
          rw [hCN]; exact h
        have h4 := (hCmem _ h3).2 n hn
        calc (g : MulAut V) * n * (g : MulAut V)⁻¹ = n * g * (g : MulAut V)⁻¹ := by rw [h4]
          _ = n := by group
    have hkcard : Nat.card φ.ker = 5 := by
      rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv, hcardN]
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hkcard] at h1
    have h2 : Nat.card φ.range ∣ 4 := by
      have := Subgroup.card_subgroup_dvd_card φ.range
      rwa [IsCyclic.card_mulAut, hcardN, Nat.totient_prime hp5] at this
    rw [← h1]
    exact (Nat.mul_dvd_mul_left 5 h2).trans (by norm_num)

end S152N2

end CFSG.Quasithin
