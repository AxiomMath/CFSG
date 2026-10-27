module

public import CFSG.LocalAnalysis.StandardType.GGKacTable

public section

namespace CFSG.StandardType

private theorem k0CompOrbit_go_eq (img : List ℕ → List ℕ) (c : List ℕ) {k : ℕ} (hk : 0 < k)
    (hper : img^[k] c = c) (hmin : ∀ m, 0 < m → m < k → img^[m] c ≠ c) :
    ∀ (f m : ℕ) (acc : List (List ℕ)), 1 ≤ m → m ≤ k → k - m ≤ f →
      k0CompOrbit.go img c f (img^[m] c) acc =
        acc ++ (List.range (k - m)).map (fun t => img^[m + t] c) := by
  intro f
  induction f with
  | zero =>
      intro m acc hm1 hmk hf
      have hmk' : m = k := by omega
      subst hmk'
      simp [k0CompOrbit.go]
  | succ f ih =>
      intro m acc hm1 hmk hf
      by_cases hmk' : m = k
      · subst hmk'
        simp [k0CompOrbit.go, hper]
      · have hmlt : m < k := by omega
        have hne : img^[m] c ≠ c := hmin m hm1 hmlt
        rw [k0CompOrbit.go, if_neg hne]
        rw [show img (img^[m] c) = img^[m + 1] c from
          (Function.iterate_succ_apply' img m c).symm]
        rw [ih (m + 1) (acc ++ [img^[m] c]) (by omega) (by omega) (by omega)]
        have hrange : List.range (k - m) = 0 :: (List.range (k - (m + 1))).map Nat.succ := by
          rw [show k - m = (k - (m + 1)) + 1 by omega, List.range_succ_eq_map]
        rw [hrange, List.map_cons, List.map_map]
        rw [show ((fun t => img^[m + t] c) ∘ Nat.succ) = (fun t => img^[(m + 1) + t] c) from by
          funext t
          simp only [Function.comp_apply]
          rw [show m + Nat.succ t = (m + 1) + t by omega]]
        simp only [List.append_assoc, List.cons_append, List.nil_append, Nat.add_zero]

theorem k0CompOrbit_spec {img : List ℕ → List ℕ} {c : List ℕ} {k fuel : ℕ} (hk : 0 < k)
    (hper : img^[k] c = c) (hmin : ∀ m, 0 < m → m < k → img^[m] c ≠ c) (hfuel : k ≤ fuel) :
    k0CompOrbit img fuel c = (List.range k).map (fun m => img^[m] c) := by
  have hgo := k0CompOrbit_go_eq img c hk hper hmin fuel 1 [c] (by omega) hk (by omega)
  unfold k0CompOrbit
  rw [show img c = img^[1] c by rw [Function.iterate_one]]
  rw [hgo]
  have hshift : (List.range k).map (fun m => img^[m] c) =
      [c] ++ (List.range (k - 1)).map (fun t => img^[1 + t] c) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.singleton_append,
      Function.iterate_zero_apply]
    congr 1
    rw [show ((fun m => img^[m] c) ∘ Nat.succ) = (fun t => img^[1 + t] c) from by
      funext t
      simp only [Function.comp_apply]
      rw [show Nat.succ t = 1 + t by omega]]
  rw [hshift]


private theorem k0CompOrbits_iterate_mem {img : List ℕ → List ℕ} {cs : List (List ℕ)}
    (hmap : ∀ x ∈ cs, img x ∈ cs) {c : List ℕ} (hc : c ∈ cs) :
    ∀ m, img^[m] c ∈ cs := by
  intro m
  simpa using Set.MapsTo.iterate (s := {x | x ∈ cs}) hmap m hc

private theorem k0CompOrbits_iterate_eq_self {img : List ℕ → List ℕ} {cs : List (List ℕ)}
    (hmap : ∀ x ∈ cs, img x ∈ cs)
    (hinj : ∀ x ∈ cs, ∀ y ∈ cs, img x = img y → x = y)
    {c : List ℕ} (hc : c ∈ cs) {i j : ℕ} (hij : i < j)
    (heq : img^[i] c = img^[j] c) :
    img^[j - i] c = c := by
  have hiter := k0CompOrbits_iterate_mem hmap hc
  have hcancel : Set.InjOn (img^[i]) {x | x ∈ cs} :=
    Set.InjOn.iterate (s := {x | x ∈ cs}) hinj hmap i
  have hval := hcancel hc (hiter (j - i)) ?_
  · exact hval.symm
  · calc
      img^[i] c = img^[j] c := heq
      _ = img^[i + (j - i)] c := by rw [show i + (j - i) = j by omega]
      _ = img^[i] (img^[j - i] c) := Function.iterate_add_apply ..

private theorem k0CompOrbits_exists_period {img : List ℕ → List ℕ} {cs : List (List ℕ)}
    (hnd : cs.Nodup) (hmap : ∀ c ∈ cs, img c ∈ cs)
    (hinj : ∀ c ∈ cs, ∀ c' ∈ cs, img c = img c' → c = c')
    {c : List ℕ} (hc : c ∈ cs) :
    ∃ k, 0 < k ∧ k ≤ cs.length ∧ img^[k] c = c := by
  have hiter := k0CompOrbits_iterate_mem hmap hc
  have hcard : (cs.toFinset).card < (Finset.range (cs.length + 1)).card := by
    rw [List.toFinset_card_of_nodup hnd, Finset.card_range]
    omega
  have hmaps : Set.MapsTo (fun m : ℕ => img^[m] c)
      (Finset.range (cs.length + 1)) cs.toFinset := by
    intro m _
    exact List.mem_toFinset.mpr (hiter m)
  obtain ⟨i, hi, j, hj, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hi' : i < cs.length + 1 := Finset.mem_range.mp hi
  have hj' : j < cs.length + 1 := Finset.mem_range.mp hj
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨j - i, by omega, by omega, k0CompOrbits_iterate_eq_self hmap hinj hc hlt heq⟩
  · exact ⟨i - j, by omega, by omega,
      k0CompOrbits_iterate_eq_self hmap hinj hc hgt heq.symm⟩

private theorem k0CompOrbits_find_period {img : List ℕ → List ℕ} {cs : List (List ℕ)}
    (hnd : cs.Nodup) (hmap : ∀ c ∈ cs, img c ∈ cs)
    (hinj : ∀ c ∈ cs, ∀ c' ∈ cs, img c = img c' → c = c')
    {c : List ℕ} (hc : c ∈ cs) :
    ∃ k, 0 < k ∧ k ≤ cs.length ∧ img^[k] c = c ∧
      ∀ m, 0 < m → m < k → img^[m] c ≠ c := by
  have hex := k0CompOrbits_exists_period hnd hmap hinj hc
  let k := Nat.find hex
  have hspec := Nat.find_spec hex
  refine ⟨k, hspec.1, hspec.2.1, hspec.2.2, ?_⟩
  intro m hm0 hmk hmeq
  have hmP : 0 < m ∧ m ≤ cs.length ∧ img^[m] c = c :=
    ⟨hm0, le_trans (le_of_lt hmk) hspec.2.1, hmeq⟩
  have hle : k ≤ m := Nat.find_min' hex hmP
  omega

private theorem k0CompOrbits_orbit_facts {img : List ℕ → List ℕ} {cs : List (List ℕ)}
    (hnd : cs.Nodup) (hmap : ∀ c ∈ cs, img c ∈ cs)
    (hinj : ∀ c ∈ cs, ∀ c' ∈ cs, img c = img c' → c = c')
    {fuel : ℕ} (hfuel : cs.length < fuel) {c : List ℕ} (hc : c ∈ cs) :
    k0CompOrbit img fuel c ≠ [] ∧ (k0CompOrbit img fuel c).Nodup ∧
      (∀ (k : ℕ) (hk : k < (k0CompOrbit img fuel c).length),
        (k0CompOrbit img fuel c)[k] = img^[k] ((k0CompOrbit img fuel c).headD [])) ∧
      img^[(k0CompOrbit img fuel c).length] ((k0CompOrbit img fuel c).headD []) =
        (k0CompOrbit img fuel c).headD [] := by
  obtain ⟨k, hk0, hkle, hper, hmin⟩ := k0CompOrbits_find_period hnd hmap hinj hc
  have horb : k0CompOrbit img fuel c = (List.range k).map (fun m => img^[m] c) :=
    k0CompOrbit_spec hk0 hper hmin (le_trans hkle (le_of_lt hfuel))
  have hhead : ((List.range k).map (fun m => img^[m] c)).headD [] = c := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [List.range_succ_eq_map, List.map_cons, List.headD_cons, Function.iterate_zero_apply]
  have hlen : ((List.range k).map (fun m => img^[m] c)).length = k := by simp
  have hnodup : ((List.range k).map (fun m => img^[m] c)).Nodup := by
    rw [List.nodup_map_iff_inj_on (List.nodup_range)]
    intro i hi j hj heq
    by_contra hne
    have hi' : i < k := List.mem_range.mp hi
    have hj' : j < k := List.mem_range.mp hj
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hmin (j - i) (by omega) (by omega)
        (k0CompOrbits_iterate_eq_self hmap hinj hc hlt heq)
    · exact hmin (i - j) (by omega) (by omega)
        (k0CompOrbits_iterate_eq_self hmap hinj hc hgt heq.symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [horb]
    intro hnil
    have h0 : ((List.range k).map (fun m => img^[m] c)).length = 0 := by rw [hnil]; rfl
    rw [hlen] at h0
    omega
  · rw [horb]; exact hnodup
  · intro j hj
    rw [List.getElem_of_eq horb hj, List.getElem_map, List.getElem_range]
    rw [show (k0CompOrbit img fuel c).headD [] = c by rw [horb]; exact hhead]
  · rw [horb, hlen, hhead, hper]

private theorem k0CompOrbits_orbit_mem_closed {img : List ℕ → List ℕ} {cs : List (List ℕ)}
    (hnd : cs.Nodup) (hmap : ∀ c ∈ cs, img c ∈ cs)
    (hinj : ∀ c ∈ cs, ∀ c' ∈ cs, img c = img c' → c = c')
    {fuel : ℕ} (hfuel : cs.length < fuel) {c : List ℕ} (hc : c ∈ cs) :
    k0CompOrbit img fuel c ⊆ cs ∧
      (∀ x ∈ k0CompOrbit img fuel c, img x ∈ k0CompOrbit img fuel c) := by
  obtain ⟨k, hk0, hkle, hper, hmin⟩ := k0CompOrbits_find_period hnd hmap hinj hc
  have horb : k0CompOrbit img fuel c = (List.range k).map (fun m => img^[m] c) :=
    k0CompOrbit_spec hk0 hper hmin (le_trans hkle (le_of_lt hfuel))
  have hiter := k0CompOrbits_iterate_mem hmap hc
  constructor
  · intro x hx
    rw [horb] at hx
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
    exact hiter m
  · intro x hx
    rw [horb] at hx ⊢
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    have hmk : m < k := List.mem_range.mp hm
    have hstep : img (img^[m] c) = img^[m + 1] c :=
      (Function.iterate_succ_apply' img m c).symm
    rw [hstep]
    by_cases hlt : m + 1 < k
    · exact List.mem_map.mpr ⟨m + 1, List.mem_range.mpr hlt, rfl⟩
    · have hk : m + 1 = k := by omega
      rw [hk, hper]
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr hk0, Function.iterate_zero_apply ..⟩

private theorem k0CompOrbits_orbit_disjoint {img : List ℕ → List ℕ} {seen : List (List ℕ)}
    (hclosed : ∀ x ∈ seen, img x ∈ seen) {fuel : ℕ} {c : List ℕ} {k : ℕ}
    (horb : k0CompOrbit img fuel c = (List.range k).map (fun m => img^[m] c))
    (hper : img^[k] c = c) (hcseen : c ∉ seen) :
    ∀ x ∈ k0CompOrbit img fuel c, x ∉ seen := by
  intro x hx hxseen
  rw [horb] at hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  have hmk : m < k := List.mem_range.mp hm
  have hmem : img^[k - m] (img^[m] c) ∈ seen :=
    k0CompOrbits_iterate_mem hclosed hxseen (k - m)
  have heq : img^[k - m] (img^[m] c) = c := by
    rw [← Function.iterate_add_apply, show k - m + m = k by omega, hper]
  exact hcseen (heq ▸ hmem)

private theorem k0CompOrbits_cons_data {img : List ℕ → List ℕ} {cs : List (List ℕ)}
    (hnd : cs.Nodup) (hmap : ∀ c ∈ cs, img c ∈ cs)
    (hinj : ∀ c ∈ cs, ∀ c' ∈ cs, img c = img c' → c = c')
    {fuel : ℕ} (hfuel : cs.length < fuel) {c : List ℕ} {rest seen : List (List ℕ)}
    (hc : c ∈ cs) (hseen_sub : seen ⊆ cs) (hseen_nd : seen.Nodup)
    (hclosed : ∀ x ∈ seen, img x ∈ seen)
    (hcover : ∀ x ∈ cs, x ∈ c :: rest ∨ x ∈ seen) (hcseen : c ∉ seen) :
    k0CompOrbit img fuel c ⊆ cs ∧
    (∀ x ∈ k0CompOrbit img fuel c, img x ∈ k0CompOrbit img fuel c) ∧
    (seen ++ k0CompOrbit img fuel c).Nodup ∧
    (seen ++ k0CompOrbit img fuel c) ⊆ cs ∧
    (∀ x ∈ seen ++ k0CompOrbit img fuel c, img x ∈ seen ++ k0CompOrbit img fuel c) ∧
    c ∈ k0CompOrbit img fuel c ∧
    (∀ x ∈ cs, x ∈ rest ∨ x ∈ seen ++ k0CompOrbit img fuel c) := by
  obtain ⟨k, hk0, hkle, hper, hmin⟩ := k0CompOrbits_find_period hnd hmap hinj hc
  have horb : k0CompOrbit img fuel c = (List.range k).map (fun m => img^[m] c) :=
    k0CompOrbit_spec hk0 hper hmin (le_trans hkle (le_of_lt hfuel))
  have hmem_o : k0CompOrbit img fuel c ⊆ cs :=
    (k0CompOrbits_orbit_mem_closed hnd hmap hinj hfuel hc).1
  have hclosed_o : ∀ x ∈ k0CompOrbit img fuel c, img x ∈ k0CompOrbit img fuel c :=
    (k0CompOrbits_orbit_mem_closed hnd hmap hinj hfuel hc).2
  have hnd_o : (k0CompOrbit img fuel c).Nodup :=
    (k0CompOrbits_orbit_facts hnd hmap hinj hfuel hc).2.1
  have hdisj : ∀ x ∈ k0CompOrbit img fuel c, x ∉ seen :=
    k0CompOrbits_orbit_disjoint hclosed horb hper hcseen
  have hcorbit : c ∈ k0CompOrbit img fuel c := by
    rw [horb]
    exact List.mem_map.mpr ⟨0, List.mem_range.mpr hk0, Function.iterate_zero_apply ..⟩
  refine ⟨hmem_o, hclosed_o, ?_, ?_, ?_, hcorbit, ?_⟩
  · exact List.nodup_append.mpr ⟨hseen_nd, hnd_o,
      fun a ha b hb heq => hdisj b hb (heq ▸ ha)⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hseen_sub hx
    · exact hmem_o hx
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (hclosed x hx)
    · exact List.mem_append_right _ (hclosed_o x hx)
  · intro x hx
    rcases hcover x hx with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (List.mem_append_right _ hcorbit)
      · exact Or.inl h
    · exact Or.inr (List.mem_append_left _ h)

private theorem k0CompOrbits_aux {img : List ℕ → List ℕ} {cs : List (List ℕ)}
    (hnd : cs.Nodup) (hmap : ∀ c ∈ cs, img c ∈ cs)
    (hinj : ∀ c ∈ cs, ∀ c' ∈ cs, img c = img c' → c = c')
    {fuel : ℕ} (hfuel : cs.length < fuel) :
    ∀ (l seen : List (List ℕ)), l ⊆ cs → seen ⊆ cs → seen.Nodup →
      (∀ x ∈ seen, img x ∈ seen) →
      (∀ x ∈ cs, x ∈ l ∨ x ∈ seen) →
      (k0CompOrbits img fuel l seen).flatten ⊆ cs ∧
      (seen ++ (k0CompOrbits img fuel l seen).flatten).Nodup ∧
      (∀ x ∈ cs, x ∈ (k0CompOrbits img fuel l seen).flatten ∨ x ∈ seen) ∧
      (∀ o ∈ k0CompOrbits img fuel l seen,
        o ≠ [] ∧ o.Nodup ∧
        (∀ (k : ℕ) (hk : k < o.length), o[k] = img^[k] (o.headD [])) ∧
        img^[o.length] (o.headD []) = o.headD []) := by
  intro l
  induction l with
  | nil =>
      intro seen hl hseen_sub hseen_nd hclosed hcover
      simp only [k0CompOrbits, List.flatten_nil, List.append_nil]
      refine ⟨by simp, hseen_nd, ?_, by simp⟩
      intro x hx
      rcases hcover x hx with h | h
      · exact absurd h (by simp)
      · exact Or.inr h
  | cons c rest ih =>
      intro seen hl hseen_sub hseen_nd hclosed hcover
      have hl' : rest ⊆ cs := fun x hx => hl (List.mem_cons_of_mem c hx)
      rw [k0CompOrbits]
      by_cases hcseen : c ∈ seen
      · rw [if_pos hcseen]
        have hcover' : ∀ x ∈ cs, x ∈ rest ∨ x ∈ seen := by
          intro x hx
          rcases hcover x hx with h | h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr hcseen
            · exact Or.inl h
          · exact Or.inr h
        exact ih seen hl' hseen_sub hseen_nd hclosed hcover'
      · rw [if_neg hcseen]
        have hc : c ∈ cs := hl (List.mem_cons_self ..)
        have hfacts := k0CompOrbits_orbit_facts hnd hmap hinj hfuel hc
        obtain ⟨hmem_o, hclosed_o, hseen', hsub', hclosed', _, hcover'⟩ :=
          k0CompOrbits_cons_data hnd hmap hinj hfuel hc hseen_sub hseen_nd hclosed hcover hcseen
        have ih' := ih (seen ++ k0CompOrbit img fuel c) hl' hsub' hseen' hclosed' hcover'
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro x hx
          rw [List.flatten_cons] at hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hmem_o hx
          · exact ih'.1 hx
        · simpa only [List.flatten_cons, List.append_assoc] using ih'.2.1
        · intro x hx
          rcases ih'.2.2.1 x hx with h | h
          · exact Or.inl (by rw [List.flatten_cons]; exact List.mem_append_right _ h)
          · rcases List.mem_append.mp h with h | h
            · exact Or.inr h
            · exact Or.inl (by rw [List.flatten_cons]; exact List.mem_append_left _ h)
        · intro o ho
          rcases List.mem_cons.mp ho with rfl | ho
          · exact hfacts
          · exact ih'.2.2.2 o ho


theorem k0CompOrbits_spec {img : List ℕ → List ℕ} {cs : List (List ℕ)} (hnd : cs.Nodup)
    (hmap : ∀ c ∈ cs, img c ∈ cs) (hinj : ∀ c ∈ cs, ∀ c' ∈ cs, img c = img c' → c = c')
    {fuel : ℕ} (hfuel : cs.length < fuel) :
    (∀ o ∈ k0CompOrbits img fuel cs [], o ≠ [] ∧ o.Nodup ∧
      (∀ (k : ℕ) (hk : k < o.length), o[k] = img^[k] (o.headD [])) ∧
      img^[o.length] (o.headD []) = o.headD []) ∧
    (k0CompOrbits img fuel cs []).flatten.Perm cs := by
  have hmain := k0CompOrbits_aux (cs := cs) (fuel := fuel) hnd hmap hinj hfuel cs []
    (fun x hx => hx) (by simp) (by simp) (by simp) (fun x hx => Or.inl hx)
  refine ⟨hmain.2.2.2, ?_⟩
  have hsub : (k0CompOrbits img fuel cs []).flatten ⊆ cs := hmain.1
  have hnd' : (k0CompOrbits img fuel cs []).flatten.Nodup := by
    simpa using hmain.2.1
  have hcover : cs ⊆ (k0CompOrbits img fuel cs []).flatten := by
    intro x hx
    rcases hmain.2.2.1 x hx with h | h
    · exact h
    · simp at h
  exact (List.perm_ext_iff_of_nodup hnd' hnd).mpr
    (fun a => ⟨fun h => hsub h, fun h => hcover h⟩)

end CFSG.StandardType

end
