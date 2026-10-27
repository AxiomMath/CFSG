module

public import CFSG.Quasithin.EmptyFaithful.S1422LocAutDefs
public import CFSG.Quasithin.EmptyFaithful.S1422LocG2M12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace S1422Loc

section Stab

variable {G : Type*} [Group G]

theorem conj_comm_mem_of_relIndex_two {A B : Subgroup G} (hidx : A.relIndex B = 2) {g : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgB : g ∈ Subgroup.normalizer (B : Set G))
    {b : G} (hb : b ∈ B) : (g * b * g⁻¹) * b⁻¹ ∈ A := by
  by_cases hbA : b ∈ A
  · have h1 : g * b * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgA b).mp hbA
    exact A.mul_mem h1 (A.inv_mem hbA)
  · have hcB : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hgB b).mp hb
    have hcA' : g * b * g⁻¹ ∉ A := fun h => hbA ((Subgroup.mem_normalizer_iff.mp hgA b).mpr h)
    obtain ⟨a, ha⟩ := (Subgroup.index_eq_two_iff).mp (show (A.subgroupOf B).index = 2 from hidx)
    have hb' : (⟨b, hb⟩ : B) ∉ A.subgroupOf B := fun h => hbA (Subgroup.mem_subgroupOf.mp h)
    have hc' : (⟨g * b * g⁻¹, hcB⟩ : B) ∉ A.subgroupOf B := fun h =>
      hcA' (Subgroup.mem_subgroupOf.mp h)
    have e1 : (⟨b, hb⟩ : B) * a ∈ A.subgroupOf B := ((ha ⟨b, hb⟩).resolve_right
      (fun h => hb' h.1)).1
    have e2 : (⟨g * b * g⁻¹, hcB⟩ : B) * a ∈ A.subgroupOf B := ((ha ⟨g * b * g⁻¹, hcB⟩).resolve_right
      (fun h => hc' h.1)).1
    have := (A.subgroupOf B).mul_mem e2 ((A.subgroupOf B).inv_mem e1)
    have e3 : ((⟨g * b * g⁻¹, hcB⟩ : B) * a) * ((⟨b, hb⟩ : B) * a)⁻¹ =
        ⟨(g * b * g⁻¹) * b⁻¹, B.mul_mem hcB (B.inv_mem hb)⟩ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [e3] at this
    exact Subgroup.mem_subgroupOf.mp this

theorem eq_one_of_pow_odd {A : Subgroup G} (hA : IsPGroup 2 A) {x : G} (hx : x ∈ A) {m : ℕ}
    (hm : Odd m) (hxm : x ^ m = 1) : x = 1 := by
  obtain ⟨j, hj⟩ := hA ⟨x, hx⟩
  have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hd1 : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxm
  have hd2 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have hcop : Nat.Coprime m (2 ^ j) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (by rcases hm with ⟨t, ht⟩; omega))))
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)

theorem commutes_of_relIndex_two_of_odd {A B : Subgroup G} (hidx : A.relIndex B = 2) {g : G}
    (hodd : Odd (orderOf g)) (hA2 : IsPGroup 2 A)
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgB : g ∈ Subgroup.normalizer (B : Set G))
    (hcA : ∀ a ∈ A, g * a = a * g) : ∀ b ∈ B, g * b = b * g := by
  intro b hb
  have h1 := conj_comm_mem_of_relIndex_two hidx hgA hgB hb
  obtain ⟨a', ha'⟩ : ∃ a' : G, a' = (g * b * g⁻¹) * b⁻¹ := ⟨_, rfl⟩
  rw [← ha'] at h1
  have hc : g * b * g⁻¹ = a' * b := by rw [ha']; group
  have hga' : g * a' = a' * g := hcA a' h1
  have hpow : ∀ k : ℕ, g ^ k * b * (g ^ k)⁻¹ = a' ^ k * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : g * a' ^ k * g⁻¹ = a' ^ k := by
        have := (Commute.pow_right (show Commute g a' from hga') k).eq
        rw [this]; group
      calc g ^ (k + 1) * b * (g ^ (k + 1))⁻¹ = g * (g ^ k * b * (g ^ k)⁻¹) * g⁻¹ := by group
        _ = g * (a' ^ k * b) * g⁻¹ := by rw [ih]
        _ = (g * a' ^ k * g⁻¹) * (g * b * g⁻¹) := by group
        _ = a' ^ k * (a' * b) := by rw [hk, hc]
        _ = a' ^ (k + 1) * b := by group
  have h2 := hpow (orderOf g)
  rw [pow_orderOf_eq_one] at h2
  have h3 : a' ^ orderOf g = 1 := by
    have : a' ^ orderOf g * b = 1 * b := by simpa using h2.symm
    exact mul_right_cancel this
  have h4 : a' = 1 := eq_one_of_pow_odd hA2 h1 hodd h3
  rw [h4] at hc
  calc g * b = (g * b * g⁻¹) * g := by group
    _ = b * g := by rw [hc]; simp

end Stab

section Count

open Classical

variable {G : Type*} [Group G] [Finite G]

noncomputable def pairSet (z w : G) : Finset G := {w, w * z}

theorem card_le_factorial_mul_of_pairs {N : Subgroup G} {z : G} (hz1 : z ≠ 1) (hz2 : z * z = 1)
    (hzc : ∀ g ∈ N, g * z = z * g) {W : Set G} {n : ℕ} (hWcard : W.ncard = 2 * n)
    (hNW : ∀ g ∈ N, ∀ w ∈ W, g * w * g⁻¹ ∈ W) (hWz : ∀ w ∈ W, w * z ∈ W)
    {K : Subgroup G} (hKN : K ≤ N)
    (hK : ∀ g ∈ N, (∀ w ∈ W, g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w * z) → g ∈ K) :
    Nat.card N ≤ n.factorial * Nat.card K := by
  have : Fintype G := Fintype.ofFinite G
  set Wf : Finset G := (Set.toFinite W).toFinset with hWf
  have hmemW : ∀ w, w ∈ Wf ↔ w ∈ W := fun w => Set.Finite.mem_toFinset _
  have hWfcard : Wf.card = 2 * n := by
    rw [← hWcard, Set.ncard_eq_toFinset_card W (Set.toFinite W)]
  set X : Finset (Finset G) := Wf.image (pairSet z) with hX
  have hXcard : X.card ≤ n := by
    have h := Finset.mul_card_image_le_card (f := pairSet z) Wf 2 (by
      intro b hb
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
      have hwz : w * z ∈ Wf := (hmemW _).mpr (hWz w ((hmemW _).mp hw))
      have hne : w ≠ w * z := fun h => hz1 (by simpa using h.symm)
      have hsub : ({w, w * z} : Finset G) ⊆ Wf.filter (fun a => pairSet z a = pairSet z w) := by
        intro a ha
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rw [Finset.mem_filter]
        rcases ha with rfl | rfl
        · exact ⟨hw, rfl⟩
        · refine ⟨hwz, ?_⟩
          unfold pairSet
          rw [mul_assoc, hz2, mul_one, Finset.pair_comm]
      calc 2 = ({w, w * z} : Finset G).card := (Finset.card_pair hne).symm
        _ ≤ _ := Finset.card_le_card hsub)
    have h2 : 2 * X.card ≤ Wf.card := h
    omega
  have hact : ∀ (g : ↥N) (s : ↥X),
      s.1.image (fun x => (g : G) * x * (g : G)⁻¹) ∈ X := by
    intro g s
    obtain ⟨w, hw, hws⟩ := Finset.mem_image.mp s.2
    refine Finset.mem_image.mpr ⟨(g : G) * w * (g : G)⁻¹,
      (hmemW _).mpr (hNW g g.2 w ((hmemW _).mp hw)), ?_⟩
    rw [← hws]
    unfold pairSet
    rw [Finset.image_insert, Finset.image_singleton]
    have hgz : (g : G) * z * (g : G)⁻¹ = z := by rw [hzc g g.2]; group
    have : (g : G) * (w * z) * (g : G)⁻¹ = (g : G) * w * (g : G)⁻¹ * z := by
      calc (g : G) * (w * z) * (g : G)⁻¹ = ((g : G) * w * (g : G)⁻¹) * ((g : G) * z * (g : G)⁻¹) := by
            group
        _ = _ := by rw [hgz]
    rw [this]
  let act : ↥N → ↥X → ↥X := fun g s => ⟨s.1.image (fun x => (g : G) * x * (g : G)⁻¹), hact g s⟩
  have act_one : ∀ s, act 1 s = s := by
    intro s
    apply Subtype.ext
    show s.1.image (fun x => ((1 : ↥N) : G) * x * ((1 : ↥N) : G)⁻¹) = s.1
    simp
  have act_mul : ∀ g h s, act (g * h) s = act g (act h s) := by
    intro g h s
    apply Subtype.ext
    show s.1.image (fun x => ((g * h : ↥N) : G) * x * ((g * h : ↥N) : G)⁻¹) =
      (s.1.image (fun x => (h : G) * x * (h : G)⁻¹)).image (fun x => (g : G) * x * (g : G)⁻¹)
    rw [Finset.image_image]
    congr 1
    funext x
    simp [mul_assoc]
  let ρ : ↥N →* Equiv.Perm ↥X :=
    { toFun := fun g =>
        { toFun := act g
          invFun := act g⁻¹
          left_inv := fun s => by rw [← act_mul, inv_mul_cancel, act_one]
          right_inv := fun s => by rw [← act_mul, mul_inv_cancel, act_one] }
      map_one' := Equiv.ext fun s => act_one s
      map_mul' := fun g h => Equiv.ext fun s => act_mul g h s }
  have hker : ρ.ker ≤ K.subgroupOf N := by
    intro g hg
    rw [Subgroup.mem_subgroupOf]
    apply hK g g.2
    intro w hw
    have hwX : pairSet z w ∈ X := Finset.mem_image.mpr ⟨w, (hmemW _).mpr hw, rfl⟩
    have h1 : ρ g ⟨pairSet z w, hwX⟩ = ⟨pairSet z w, hwX⟩ := by
      rw [MonoidHom.mem_ker] at hg
      rw [hg]; rfl
    have h2 := congrArg Subtype.val h1
    have h3 : (g : G) * w * (g : G)⁻¹ ∈ (pairSet z w).image (fun x => (g : G) * x * (g : G)⁻¹) :=
      Finset.mem_image.mpr ⟨w, by simp [pairSet], rfl⟩
    have h4 : (ρ g ⟨pairSet z w, hwX⟩ : ↥X).1 = (pairSet z w).image (fun x => (g : G) * x * (g : G)⁻¹) := rfl
    rw [h4] at h2
    rw [h2] at h3
    simpa [pairSet] using h3
  have hrange : Nat.card ρ.range ≤ n.factorial := by
    calc Nat.card ρ.range ≤ Nat.card (Equiv.Perm ↥X) := Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = (Nat.card ↥X).factorial := Nat.card_perm
      _ ≤ n.factorial := by
        apply Nat.factorial_le
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        exact hXcard
  have hkerK : Nat.card ρ.ker ≤ Nat.card K := by
    calc Nat.card ρ.ker ≤ Nat.card (K.subgroupOf N) := Subgroup.card_le_of_le hker
      _ = Nat.card K := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  calc Nat.card N = ρ.ker.index * Nat.card ρ.ker := (Subgroup.index_mul_card ρ.ker).symm
    _ = Nat.card ρ.range * Nat.card ρ.ker := by rw [Subgroup.index_ker]
    _ ≤ n.factorial * Nat.card K := Nat.mul_le_mul hrange hkerK

end Count

theorem card_eq_384_of_isAutM12Vertex {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    (h : IsAutM12Vertex L) : Nat.card L = 384 := by
  obtain ⟨⟨φ, hφs, hφQ⟩, -, -⟩ := h
  have h1 : Nat.card ↥φ.ker = 32 := hφQ.1
  have h2 : Nat.card ↥φ.range = 12 := by
    rw [MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top, Nat.card_eq_fintype_card,
      DihedralGroup.card]
  calc Nat.card L = φ.ker.index * Nat.card φ.ker := (Subgroup.index_mul_card _).symm
    _ = Nat.card φ.range * Nat.card φ.ker := by rw [Subgroup.index_ker]
    _ = 384 := by rw [h1, h2]

end S1422Loc

open S1422Loc

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem autM12_local (hVQ : Stage1426VleQ) (hL : AutM12AmalgamLocal)
    (S : Setting1422 T M Y H) (hC : CaseAutM12 H (Y ⊔ T)) :
    H = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨hF8, hFel, hlat, hU, E, hEU, hEa, hE8, hEN, hVE⟩ := hL G H (Y ⊔ T) hC
  obtain ⟨-, hq, hvert, -, -⟩ := hC
  have hH384 : Nat.card H = 384 := card_eq_384_of_isAutM12Vertex hvert
  have hP64 : Nat.card (pCoreOf 2 H) = 64 := by
    have := hvert.2.1
    rw [this]; norm_num
  obtain ⟨z, hz, hz1, hz2, hZ⟩ := S.exists_z
  have hzz : z * z = 1 := by simpa [sq] using hz2
  have hzcen : z ∈ centerOf (pCoreOf 2 H) := by
    obtain ⟨Pp, hPp⟩ := S.exists_sylow
    exact omegaOneCenter_le_centerOf_pCoreOf H Pp (hPp ▸ S.T_le_H) S.charTwo_H (hPp ▸ hz)
  have hZP : ∀ w ∈ centerOf (pCoreOf 2 H), w = 1 ∨ w = z := by
    intro w hw
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · right
      obtain ⟨x, -, hx2⟩ := (Nat.card_eq_two_iff' (1 : ↥(centerOf (pCoreOf 2 H)))).mp hvert.2.2
      have h1 : (⟨w, hw⟩ : ↥(centerOf (pCoreOf 2 H))) = x :=
        hx2 _ (fun h => hw1 (congrArg Subtype.val h))
      have h2 : (⟨z, hzcen⟩ : ↥(centerOf (pCoreOf 2 H))) = x :=
        hx2 _ (fun h => hz1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
  have hcomZ : ∀ w ∈ centerOf (pCoreOf 2 H), w ∈ quasithinOmegaOneCenter T := by
    intro w hw
    rcases hZP w hw with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact hz
  set Mc : Subgroup G := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) with hMcdef
  set P : Subgroup G := pCoreOf 2 H with hPdef
  set F : Subgroup G := secondCenterOf P with hFdef
  set Q : Subgroup G := pCoreOf 2 Mc with hQdef
  have hHMc : H ≤ Mc := S.H_le_centralizer
  have hPH : P ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hQP : Q ≤ P := S.pCoreOf_Mc_le
  have hQMc : Q ≤ Mc := CFSG.LieType.BorelTits.pCoreOf_le 2 Mc
  have hMcQ : Mc ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Mc
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := hHMc.trans hMcQ
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hFQ : F ≤ Q := by
    intro x hx
    exact S.mem_pCoreOf_Mc_of_comm_mem (hHMc (hPH hx.1)) fun q hq => hcomZ _ (hx.2 q (hQP hq))
  have hzF : z ∈ F := ⟨hzcen.1, fun y hy => by
    have : z * y * z⁻¹ * y⁻¹ = 1 := by
      have hc : z * y = y * z := (Subgroup.mem_centralizer_iff.mp hzcen.2 y hy).symm
      rw [hc]; group
    rw [this]; exact Subgroup.one_mem _⟩
  have hzQ : z ∈ Q := hFQ hzF
  have hzc : ∀ g ∈ Mc, g * z = z * g := fun g hg => mem_Mc_comm hz hg
  have key : ∀ g q : G, q ∈ Q → (g * q * g⁻¹ = q ∨ g * q * g⁻¹ = q * z) →
      g * q * g⁻¹ * q⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro g q hq h
    rcases h with h | h
    · rw [h]
      have : q * q⁻¹ = 1 := by group
      rw [this]; exact Subgroup.one_mem _
    · rw [h]
      have hqz : q * z = z * q := mem_Mc_comm hz (hQMc hq)
      have : q * z * q⁻¹ = z := by rw [hqz]; group
      rw [this]; exact hz
  have hcardMc : 384 ≤ Nat.card Mc := hH384 ▸ Subgroup.card_le_of_le hHMc
  have hfac4 : Nat.factorial 4 = 24 := by decide
  rcases hlat Q hFQ hQP hHQ with hQF | ⟨hQ16, hQinv⟩ | hUQ
  ·
    exfalso
    have hQ8 : Nat.card Q = 8 := by rw [hQF]; exact hF8
    have hWcard : (Q : Set G).ncard = 2 * 4 := by
      rw [← Nat.card_coe_set_eq]; exact hQ8
    have hle := card_le_factorial_mul_of_pairs (N := Mc) (z := z) (W := (Q : Set G)) (n := 4)
      hz1 hzz hzc hWcard
      (fun g hg w hw => (Subgroup.mem_normalizer_iff.mp (hMcQ hg) w).mp hw)
      (fun w hw => Q.mul_mem hw hzQ) hQMc (fun g hg hgW =>
        S.mem_pCoreOf_Mc_of_comm_mem hg fun q hq => key g q hq (hgW q hq))
    rw [hfac4, hQ8] at hle
    omega
  ·
    set W : Set G := {x | x ∈ Q ∧ x * x ≠ 1} with hW
    have hWeq : W = (Q : Set G) \ (F : Set G) := by
      ext x
      constructor
      · rintro ⟨hxQ, hx1⟩
        exact ⟨hxQ, fun hxF => hx1 (hFel x hxF)⟩
      · rintro ⟨hxQ, hxF⟩
        exact ⟨hxQ, fun h => hxF (hQinv x hxQ h)⟩
    have hWcard : W.ncard = 2 * 4 := by
      have e1 : (Q : Set G).ncard = 16 := by rw [← Nat.card_coe_set_eq]; exact hQ16
      have e2 : (F : Set G).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hF8
      rw [hWeq, Set.ncard_sdiff (show (F : Set G) ⊆ (Q : Set G) from hFQ) (Set.toFinite _)]
      omega
    have hWnonempty : W.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hWcard]; norm_num)
    have hNW : ∀ g ∈ Mc, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
      intro g hg w hw
      obtain ⟨hwQ, hw1⟩ := hw
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMcQ hg) w).mp hwQ, fun h => hw1 ?_⟩
      have h2 : g * (w * w) * g⁻¹ = 1 := by
        calc g * (w * w) * g⁻¹ = (g * w * g⁻¹) * (g * w * g⁻¹) := by group
          _ = 1 := h
      have h3 : g * (w * w) = g * 1 := by
        rw [mul_one]; exact mul_inv_eq_one.mp h2
      exact mul_left_cancel h3
    have hWz : ∀ w ∈ W, w * z ∈ W := by
      rintro w ⟨hwQ, hw1⟩
      refine ⟨Q.mul_mem hwQ hzQ, fun h => hw1 ?_⟩
      have hwz : w * z = z * w := mem_Mc_comm hz (hQMc hwQ)
      calc w * w = (w * w) * (z * z) := by rw [hzz, mul_one]
        _ = (w * z) * (w * z) := by
          calc (w * w) * (z * z) = w * (w * z) * z := by group
            _ = w * (z * w) * z := by rw [hwz]
            _ = (w * z) * (w * z) := by group
        _ = 1 := h
    have hK : ∀ g ∈ Mc, (∀ w ∈ W, g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w * z) → g ∈ Q := by
      intro g hg hgW
      apply S.mem_pCoreOf_Mc_of_comm_mem hg
      intro q hq
      by_cases hqW : q ∈ W
      · exact key g q hq (hgW q hqW)
      · obtain ⟨w, hw⟩ := hWnonempty
        have hqq : q * q = 1 := by
          by_contra h
          exact hqW ⟨hq, h⟩
        have hqF : q ∈ F := hQinv q hq hqq
        have hwqW : w * q ∈ W := by
          refine ⟨Q.mul_mem hw.1 hq, fun h => hw.2 ?_⟩
          have h1 : w * q ∈ F := hQinv _ (Q.mul_mem hw.1 hq) h
          have hwF : w ∈ F := by
            have := F.mul_mem h1 (F.inv_mem hqF)
            simpa using this
          exact hFel w hwF
        have hqz : q * z = z * q := mem_Mc_comm hz (hQMc hq)
        have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
        have e : g * q * g⁻¹ * q⁻¹ = (g * w * g⁻¹)⁻¹ * (g * (w * q) * g⁻¹) * q⁻¹ := by group
        rw [e]
        have hqzq : q * z * q⁻¹ = z := by rw [hqz]; group
        rcases hgW w hw with h1 | h1 <;> rcases hgW (w * q) hwqW with h2 | h2
        · rw [h1, h2]
          have : w⁻¹ * (w * q) * q⁻¹ = 1 := by group
          rw [this]; exact Subgroup.one_mem _
        · rw [h1, h2]
          have : w⁻¹ * (w * q * z) * q⁻¹ = z := by
            calc w⁻¹ * (w * q * z) * q⁻¹ = q * z * q⁻¹ := by group
              _ = z := hqzq
          rw [this]; exact hz
        · rw [h1, h2]
          have : (w * z)⁻¹ * (w * q) * q⁻¹ = z⁻¹ := by group
          rw [this, hzi]; exact hz
        · rw [h1, h2]
          have : (w * z)⁻¹ * (w * q * z) * q⁻¹ = z⁻¹ * (q * z * q⁻¹) := by group
          rw [this, hqzq, hzi, hzz]; exact Subgroup.one_mem _
    have hle := card_le_factorial_mul_of_pairs (N := Mc) (z := z) (W := W) (n := 4)
      hz1 hzz hzc hWcard hNW hWz hQMc hK
    rw [hfac4, hQ16] at hle
    exact Subgroup.eq_of_le_of_card_ge hHMc (by omega)
  ·
    set U : Subgroup G := omegaOneOf P with hUdef
    have hU32 : Nat.card U = 32 := hU.1
    have hUP : U ≤ P := (Subgroup.closure_le _).mpr fun x hx => hx.1
    have hdvd1 : Nat.card U ∣ Nat.card Q := Subgroup.card_dvd_of_le hUQ
    have hdvd2 : Nat.card Q ∣ Nat.card P := Subgroup.card_dvd_of_le hQP
    have hQcases : Nat.card Q = 32 ∨ Nat.card Q = 64 := by
      obtain ⟨k, hk⟩ := hdvd1
      rw [hU32] at hk
      rw [hP64, hk] at hdvd2
      have hk2 : k ∣ 2 := by
        have : 32 * k ∣ 32 * 2 := by simpa using hdvd2
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      have hk3 : k ≤ 2 := Nat.le_of_dvd (by norm_num) hk2
      have hk0 : k ≠ 0 := by
        rintro rfl
        have : Nat.card Q ≠ 0 := Nat.card_pos.ne'
        omega
      interval_cases k <;> omega
    have hinvQ : ∀ x ∈ P, x ^ 2 = 1 → x ∈ Q := fun x hx hx2 =>
      hUQ (Subgroup.subset_closure ⟨hx, hx2⟩)
    have hMcU : Mc ≤ Subgroup.normalizer (U : Set G) := by
      refine le_normalizer_of_forall_conj_mem fun g hg x hx => ?_
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨hyP, hy2⟩ := hy
        apply Subgroup.subset_closure
        refine ⟨hQP ((Subgroup.mem_normalizer_iff.mp (hMcQ hg) y).mp (hinvQ y hyP hy2)), ?_⟩
        calc (g * y * g⁻¹) ^ 2 = (g * y * g⁻¹) * (g * y * g⁻¹) := sq _
          _ = g * (y * y) * g⁻¹ := by group
          _ = g * y ^ 2 * g⁻¹ := by rw [sq]
          _ = 1 := by rw [hy2]; group
      | one => simp
      | mul a b _ _ iha ihb =>
        have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [this]; exact U.mul_mem iha ihb
      | inv a _ iha =>
        have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [this]; exact U.inv_mem iha
    have hCU : ∀ x ∈ Mc, Odd (orderOf x) → (∀ u ∈ U, x * u = u * x) → x = 1 := by
      intro x hx hodd hxc
      have hxQ : ∀ q ∈ Q, x * q = q * x := by
        rcases hQcases with h32 | h64
        · have hQU : U = Q := Subgroup.eq_of_le_of_card_ge hUQ (by omega)
          intro q hq
          exact hxc q (hQU ▸ hq)
        · have hidx : U.relIndex Q = 2 := by
            have := card_eq_card_mul_relIndex hUQ
            rw [h64, hU32] at this
            omega
          exact commutes_of_relIndex_two_of_odd hidx hodd (hP2.to_le hUP) (hMcU hx) (hMcQ hx) hxc
      have hx' : x ∈ pCoreOf 2 Mc := S.charTwo_Mc ⟨hx, Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (hxQ q hq).symm⟩
      exact eq_one_of_odd_of_mem_pCoreOf hx' hodd
    have hVE' : VZ T M ≤ E :=
      hVE _ (hVQ G T M S.hyp H S.star) S.hyp.rank_two
        (S.YT_le_M.trans (le_normalizer_conjClosure _ _))
    exact S.eq_Mc_of_E hU hEU hEa hE8 hEN hVE' hMcU hCU (S.index_H_eq_three hq)

end Setting1422

end CFSG.Quasithin
