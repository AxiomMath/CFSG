module

public import CFSG.Quasithin.EmptyFaithful.S151S9E
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1.SporadicPerm

section Center

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem cmax_center_of_baseCert (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (qs : List (Γ × Γ))
    (z g gi h hi : Γ) (Ts : Array (List ℕ)) (par cl : Array ℕ) (k : ℕ)
    (hcert : BaseCert n B (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray))
      (tab n z).toArray (tab n g).toArray (tab n gi).toArray (tab n h).toArray
      (tab n hi).toArray Ts par cl k) :
    ∀ c ∈ Subgroup.closure {x | x ∈ qs.map Prod.fst},
      (∀ q ∈ Subgroup.closure {x | x ∈ qs.map Prod.fst}, c * q = q * c) → c = 1 ∨ c = z := by
  obtain ⟨hinv, -, -, hEnum, -, hcen, -, -, -⟩ := hcert
  have hinv_of : ∀ x y : Γ,
      (∀ q < n, img (tab n y).toArray (img (tab n x).toArray q) = q) → y = x⁻¹ := by
    intro x y hxy
    apply eq_inv_of_mul_eq_one_left
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb)]
    have := hxy b (hB b hb)
    simpa only [img_tab] using this
  have hqsinv : ∀ p ∈ qs, p.2 = p.1⁻¹ := fun p hp =>
    hinv_of p.1 p.2 (hinv _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  let gens : List Γ := qs.map Prod.fst
  have hG : (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray)).map Prod.fst =
      genTabs n gens := by
    simp only [genTabs, gens, List.map_map, Function.comp_def]
  have hGi : (qs.map fun p => ((tab n p.1).toArray, (tab n p.2).toArray)).map Prod.snd =
      genTabsInv n gens := by
    simp only [genTabsInv, gens, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    rw [hqsinv p hp]
  rw [hG, hGi] at hEnum
  rw [hG] at hcen
  have hP : ∀ p ∈ ptsOf B (genTabs n gens), p < n := ptsOf_lt hB gens
  have hBP : ∀ b ∈ B, b ∈ ptsOf B (genTabs n gens) := fun b hb => List.mem_append_left _ hb
  have hQmem : ∀ x : Γ, x ∈ Subgroup.closure {x | x ∈ gens} →
      rt n (ptsOf B (genTabs n gens)) x ∈ Ts.toList := fun x hx =>
    benum_closed hB gens Ts par cl hEnum x hx
  intro c hcQ hcc
  have hcT : rt n (ptsOf B (genTabs n gens)) c ∈ Ts.toList := hQmem c hcQ
  have hcomm := rt_comm_clause hB gens c fun s hs => hcc s (Subgroup.subset_closure hs)
  rcases hcen _ hcT hcomm with h1 | h1
  · left
    exact rt_injective hB hBP hbase (by rw [h1, rt_one hP])
  · right
    exact rt_injective hB hBP hbase (by rw [h1, rt_one_mul hP])

theorem cmax_center_of_baseCertS (B : List ℕ) (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ)) (zn gn gin hn hin : ℕ)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k : ℕ)
    (hcert : BaseCertS n B (slpTabsA (tab n a).toArray (tab n b).toArray prog) qp zn gn gin hn hin
      Ts par cl k) :
    ∀ c ∈ Subgroup.closure {x | x ∈ qp.map fun p => (slpElts a b prog).getD p.1 1},
      (∀ q ∈ Subgroup.closure {x | x ∈ qp.map fun p => (slpElts a b prog).getD p.1 1},
        c * q = q * c) → c = 1 ∨ c = (slpElts a b prog).getD zn 1 := by
  obtain ⟨hqp, hz, hg, hgi, hh, hhi, hc⟩ := hcert
  set T := slpTabsA (tab n a).toArray (tab n b).toArray prog with hT
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) hv
  have hE : ∀ i < T.size, tab n ((slpElts a b prog).getD i 1) = (T[i]!).toList := hinv.2
  have hE' : ∀ i < T.size, (tab n ((slpElts a b prog).getD i 1)).toArray = T[i]! := by
    intro i hi
    rw [hE i hi, Array.toArray_toList]
  have key := cmax_center_of_baseCert B hB hbase
    (qp.map fun p => ((slpElts a b prog).getD p.1 1, (slpElts a b prog).getD p.2 1))
    ((slpElts a b prog).getD zn 1) ((slpElts a b prog).getD gn 1) ((slpElts a b prog).getD gin 1)
    ((slpElts a b prog).getD hn 1) ((slpElts a b prog).getD hin 1) Ts par cl k
  rw [hE' zn hz, hE' gn hg, hE' gin hgi, hE' hn hh, hE' hin hhi] at key
  have hmap : (qp.map fun p => ((slpElts a b prog).getD p.1 1, (slpElts a b prog).getD p.2 1)).map
      (fun p => ((tab n p.1).toArray, (tab n p.2).toArray)) =
        qp.map fun p => (T[p.1]!, T[p.2]!) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    rw [hE' p.1 (hqp p hp).1, hE' p.2 (hqp p hp).2]
  have hfst : (qp.map fun p => ((slpElts a b prog).getD p.1 1, (slpElts a b prog).getD p.2 1)).map
      Prod.fst = qp.map fun p => (slpElts a b prog).getD p.1 1 := by
    rw [List.map_map]
    rfl
  rw [hmap, hfst] at key
  exact key hc

end Center

section Order

variable {Γ : Type} [Group Γ]

theorem cmax_center_eq_zpowers [Finite Γ] {S : Subgroup Γ} {z : Γ} (hS : IsPGroup 2 ↥S)
    (hnt : Nontrivial ↥S)
    (hc : ∀ c ∈ S, (∀ q ∈ S, c * q = q * c) → c = 1 ∨ c = z) :
    orderOf z = 2 ∧ centerOf S = Subgroup.zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcn : Nontrivial (Subgroup.center ↥S) := hS.center_nontrivial
  obtain ⟨⟨c, hcmem⟩, hc1⟩ := exists_ne (1 : Subgroup.center ↥S)
  have hcS : (c : Γ) ∈ S := c.2
  have hcc : ∀ q ∈ S, (c : Γ) * q = q * (c : Γ) := fun q hq => by
    have := Subgroup.mem_center_iff.mp hcmem ⟨q, hq⟩
    exact congrArg Subtype.val this.symm
  have hcne : (c : Γ) ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hcz : (c : Γ) = z := (hc _ hcS hcc).resolve_left hcne
  have hzS : z ∈ S := hcz ▸ hcS
  have hzc : ∀ q ∈ S, z * q = q * z := hcz ▸ hcc
  have hz1 : z ≠ 1 := hcz ▸ hcne
  have hz2 : z * z = 1 := by
    have hzz : z * z ∈ S := S.mul_mem hzS hzS
    have hzzc : ∀ q ∈ S, z * z * q = q * (z * z) := fun q hq => by
      rw [mul_assoc, hzc q hq, ← mul_assoc, hzc q hq, mul_assoc]
    rcases hc _ hzz hzzc with h | h
    · exact h
    · exact absurd (mul_right_cancel (h.trans (one_mul z).symm)) hz1
  refine ⟨orderOf_eq_prime (by rw [sq]; exact hz2) hz1, ?_⟩
  apply le_antisymm
  · rintro x ⟨hxS, hxc⟩
    rcases hc x hxS (fun q hq => (Subgroup.mem_centralizer_iff.mp hxc q hq).symm) with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers z
  · rw [Subgroup.zpowers_le]
    exact ⟨hzS, Subgroup.mem_centralizer_iff.mpr fun q hq => (hzc q hq).symm⟩

theorem cmax_isMaxSubgroupIn_of_orders [Finite Γ] {T Y : Subgroup Γ} (hTY : T ≤ Y) (hY : Y ≠ ⊤)
    (L : List ℕ) (hlat : ∀ K : Subgroup Γ, T ≤ K → K = ⊤ ∨ Nat.card K ∈ L)
    (hdiv : ∀ m ∈ L, Nat.card Y ∣ m → m = Nat.card Y) : IsMaxSubgroupIn ⊤ Y := by
  refine ⟨lt_top_iff_ne_top.mpr hY, fun K hYK _ => ?_⟩
  rcases hlat K (hTY.trans hYK.le) with h | h
  · exact h
  · exfalso
    have hd : Nat.card Y ∣ Nat.card K := Subgroup.card_dvd_of_le hYK.le
    have heq := hdiv _ h hd
    exact hYK.ne (Subgroup.eq_of_le_of_card_ge hYK.le (by rw [heq]))

theorem cmax_le_centralizer_of_center {S : Subgroup Γ} {z : Γ}
    (hZ : centerOf S = Subgroup.zpowers z) : S ≤ Subgroup.centralizer ({z} : Set Γ) := by
  intro s hs
  have hzmem : z ∈ centerOf S := hZ ▸ Subgroup.mem_zpowers z
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp hzmem.2 s hs

theorem cmax_centMaxProp_of_lattice [Finite Γ] {S : Subgroup Γ} {z : Γ} (hS2 : IsPGroup 2 ↥S)
    (hSi : ¬ 2 ∣ S.index) (hz2 : orderOf z = 2) (hZ : centerOf S = Subgroup.zpowers z)
    (L : List ℕ) (hlat : ∀ K : Subgroup Γ, S ≤ K → K = ⊤ ∨ Nat.card K ∈ L)
    (hdiv : ∀ m ∈ L, Nat.card (Subgroup.centralizer ({z} : Set Γ)) ∣ m →
      m = Nat.card (Subgroup.centralizer ({z} : Set Γ)))
    (hne : Nat.card (Subgroup.centralizer ({z} : Set Γ)) ≠ Nat.card Γ) : CentMaxProp Γ := by
  have hSC := cmax_le_centralizer_of_center hZ
  have hnt : Subgroup.centralizer ({z} : Set Γ) ≠ ⊤ := fun h => hne (by rw [h, Subgroup.card_top])
  exact centMaxProp_of_data hS2 hSi hz2 hZ (cmax_isMaxSubgroupIn_of_orders hSC hnt L hlat hdiv)

theorem cmax_card_centralizer_equiv {Γ' : Type*} [Group Γ'] (φ : Γ ≃* Γ') (t : Γ) :
    Nat.card (Subgroup.centralizer ({t} : Set Γ)) =
      Nat.card (Subgroup.centralizer ({φ t} : Set Γ')) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨φ g, ?_⟩
      invFun := fun g => ⟨φ.symm g, ?_⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }
  · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp g.2]
  · have h := Subgroup.mem_centralizer_singleton_iff.mp g.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h]

theorem cmax_isMaxSubgroupIn_centralizer_of_equiv {Γ' : Type} [Group Γ'] (φ : Γ ≃* Γ') {t : Γ}
    (h : IsCoatom (Subgroup.centralizer ({φ t} : Set Γ'))) :
    IsMaxSubgroupIn ⊤ (Subgroup.centralizer ({t} : Set Γ)) := by
  have h1 : IsMaxSubgroupIn ⊤ (Subgroup.centralizer ({φ t} : Set Γ')) :=
    ⟨lt_top_iff_ne_top.mpr h.1, fun L hKL _ => h.2 L hKL⟩
  have h2 := isMaxSubgroupIn_map φ.symm h1
  have h3 : (Subgroup.centralizer ({φ t} : Set Γ')).map φ.symm.toMonoidHom =
      Subgroup.centralizer ({t} : Set Γ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply φ.injective
      simpa using hy'
    · intro hx
      refine ⟨φ x, ?_, by simp⟩
      have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
      show φ x ∈ Subgroup.centralizer ({φ t} : Set Γ')
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx']
  rwa [h3] at h2

end Order

end CFSG.Quasithin
