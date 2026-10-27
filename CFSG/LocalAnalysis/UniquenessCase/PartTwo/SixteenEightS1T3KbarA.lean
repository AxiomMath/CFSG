module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarFano
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarIdx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

theorem s16t3_index_eq_two_of_thirds {G : Type*} [Group G] (S : Subgroup G)
    (h : ∀ x y z : G, x⁻¹ * y ∈ S ∨ x⁻¹ * z ∈ S ∨ y⁻¹ * z ∈ S) :
    S = ⊤ ∨ S.index = 2 := by
  by_cases htop : S = ⊤
  · exact Or.inl htop
  · refine Or.inr ?_
    have hex : ∃ a : G, a ∉ S := by
      by_contra hc
      exact htop (eq_top_iff.2 fun x _ => by
        by_contra hx
        exact hc ⟨x, hx⟩)
    obtain ⟨a, ha⟩ := hex
    rw [Subgroup.index_eq_two_iff_exists_notMem_and']
    refine ⟨a, ha, fun b => ?_⟩
    rcases h a (a * b) 1 with h2 | h2 | h2
    · right
      have h2' : a⁻¹ * (a * b) = b := by group
      rwa [h2'] at h2
    · exfalso
      have h2' : a⁻¹ * 1 = a⁻¹ := by group
      rw [h2'] at h2
      exact ha (by simpa using S.inv_mem h2)
    · left
      have h2' : (a * b)⁻¹ * 1 = (a * b)⁻¹ := by group
      rw [h2'] at h2
      simpa using S.inv_mem h2

theorem s16t3_gl3_index_two {R : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))}
    (htrans : ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 →
      ∃ k ∈ R, (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec u = v)
    {S : Subgroup ↥R}
    (hprop : ∀ x y z : ↥R, x⁻¹ * y ∈ S ∨ x⁻¹ * z ∈ S ∨ y⁻¹ * z ∈ S) :
    S = ⊤ := by
  haveI : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := s16t3_gl3_isSimpleGroup
  rcases s16t3_index_eq_two_of_thirds S hprop with htop | hidx
  · exact htop
  · exfalso
    rcases s16t3_gl3_transitive_card R htrans with h7 | h21 | htopR
    · have hcard := S.card_mul_index
      rw [hidx, h7] at hcard
      omega
    · have hcard := S.card_mul_index
      rw [hidx, h21] at hcard
      omega
    · haveI : IsSimpleGroup ↥R := by
        rw [htopR]
        exact (Subgroup.topEquiv (G := Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))).isSimpleGroup
      have hN : S.Normal := Subgroup.normal_of_index_eq_two hidx
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with hbot | htopS
      · have hcard := S.card_mul_index
        rw [hidx, hbot, Subgroup.card_bot] at hcard
        have h168 : Nat.card ↥R = 168 := by
          rw [htopR, Subgroup.card_top, CFSG.ComponentClassification.GHarris.card_GL32_gh]
        rw [h168] at hcard
        omega
      · rw [htopS, Subgroup.index_top] at hidx
        omega

theorem s16t3_structure_of_seven (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7) :
    ∃ N : Subgroup (MulAut W), N ≤ A ∧ L ≤ N ∧
      (∀ a ∈ N, ∀ I ∈ irrSet L, I.map a.toMonoidHom = I) ∧
      (∀ n ∈ N, ∀ k ∈ s1t3KBar A L, n * k = k * n) ∧ N ⊓ s1t3KBar A L = ⊥ ∧ N ⊔ s1t3KBar A L = A ∧
      (Nat.card ↥(s1t3KBar A L) = 7 ∨ Nat.card ↥(s1t3KBar A L) = 21 ∨
        (Nat.card ↥(s1t3KBar A L) = 168 ∧ IsSimpleGroup ↥(s1t3KBar A L))) := by
  classical
  haveI : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := s16t3_gl3_isSimpleGroup
  obtain ⟨r, hr1, hrtrans⟩ := h.exists_fano_rep h7
  let K : Subgroup (MulAut W) := s1t3KBar A L
  have hKA : K ≤ A := inf_le_left
  let K' : Subgroup ↥A := K.subgroupOf A
  let L' : Subgroup ↥A := L.subgroupOf A
  let N : Subgroup (MulAut W) := r.ker.map A.subtype
  have hK'map : K'.map A.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKA
  have hstab : ∀ l ∈ L, ∀ J ∈ irrSet L, J.map l.toMonoidHom = J := by
    intro l hl J hJ
    have hstable : L ≤ stabSub J := fun x hx => by
      rw [mem_stabSub]
      intro u
      constructor
      · intro hxu
        have h1 := hJ.2.2.1 x⁻¹ (L.inv_mem hx) (x u) hxu
        simpa [MulAut.mul_apply] using h1
      · intro hu
        exact hJ.2.2.1 x hx u hu
    exact (StabLat.mem_stabSub_iff_map).1 (hstable hl)
  have hLker : L' ≤ r.ker := by
    intro l' hl'
    rw [MonoidHom.mem_ker, hr1]
    intro J hJ
    exact hstab (l' : MulAut W) hl' J hJ
  have hNle : N ≤ A := Subgroup.map_subtype_le r.ker
  have hLleN : L ≤ N := by
    intro l hl
    exact Subgroup.mem_map.2 ⟨⟨l, h.le hl⟩, by
      rw [MonoidHom.mem_ker, hr1]
      intro J hJ
      exact hstab l hl J hJ, rfl⟩
  have hNfix : ∀ a ∈ N, ∀ I ∈ irrSet L, I.map a.toMonoidHom = I := by
    intro a ha I hI
    rcases Subgroup.mem_map.1 ha with ⟨x, hx, rfl⟩
    exact (hr1 x).1 hx I hI
  have hkerK' : r.ker ⊓ K' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (h.eq_one_of_kBar_fix hx.2 ((hr1 x).1 hx.1))
  have hNK : N ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rcases hx with ⟨hxN, hxK⟩
    rcases Subgroup.mem_map.1 hxN with ⟨n', hn', rfl⟩
    exact h.eq_one_of_kBar_fix hxK ((hr1 n').1 hn')
  have hNnormal : (N.subgroupOf A).Normal := by
    have heq : N.subgroupOf A = r.ker := by
      change (r.ker.map A.subtype).comap A.subtype = r.ker
      rw [Subgroup.comap_map_eq_self_of_injective A.subtype_injective]
    rw [heq]
    exact MonoidHom.normal_ker r
  have hKnormal : (K.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKA]
    intro x a hx ha
    refine ⟨A.mul_mem (A.mul_mem ha hx.1) (A.inv_mem ha), ?_⟩
    change a * x * a⁻¹ ∈ Subgroup.centralizer (L : Set (MulAut W))
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : a⁻¹ * l * a ∈ L := ((Subgroup.mem_normalizer_iff''.mp (h.normal ha)) l).1 hl
    have hcomm : (a⁻¹ * l * a) * x = x * (a⁻¹ * l * a) :=
      (Subgroup.mem_centralizer_iff.1 hx.2) (a⁻¹ * l * a) hl'
    calc l * (a * x * a⁻¹)
        = a * ((a⁻¹ * l * a) * x) * a⁻¹ := by group
      _ = a * (x * (a⁻¹ * l * a)) * a⁻¹ := by rw [hcomm]
      _ = (a * x * a⁻¹) * l := by group
  have hcommNK : ∀ n ∈ N, ∀ k ∈ K, n * k = k * n := by
    intro n hn k hk
    have hnA : n ∈ A := hNle hn
    have hkn : n * k * n⁻¹ ∈ K :=
      ((Subgroup.normal_subgroupOf_iff hKA).1 hKnormal) k n hk hnA
    have hkn' : k * n⁻¹ * k⁻¹ ∈ N :=
      ((Subgroup.normal_subgroupOf_iff hNle).1 hNnormal) n⁻¹ k (N.inv_mem hn) (hKA hk)
    have hmemK : n * k * n⁻¹ * k⁻¹ ∈ K := K.mul_mem hkn (K.inv_mem hk)
    have hmemN : n * k * n⁻¹ * k⁻¹ ∈ N := by
      have h' := N.mul_mem hn hkn'
      simpa [mul_assoc] using h'
    have hbot : n * k * n⁻¹ * k⁻¹ ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hNK]
      exact ⟨hmemN, hmemK⟩
    have hone : n * k * n⁻¹ * k⁻¹ = 1 := by simpa using hbot
    calc n * k = (n * k * n⁻¹ * k⁻¹) * (k * n) := by group
      _ = 1 * (k * n) := by rw [hone]
      _ = k * n := by group
  let R : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := r.range
  let S : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := K'.map r
  have hSleR : S ≤ R := Subgroup.map_le_range r K'
  let SR : Subgroup ↥R := S.subgroupOf R
  have hmapLK : ((L ⊔ K).subgroupOf A).map r = S := by
    have hL'bot : (L.subgroupOf A).map r = ⊥ :=
      (Subgroup.map_eq_bot_iff (L.subgroupOf A) (f := r)).mpr hLker
    rw [Subgroup.subgroupOf_sup h.le hKA, Subgroup.map_sup, hL'bot, bot_sup_eq]
  have hkey : ∀ p q : ↥A, (p : MulAut W)⁻¹ * (q : MulAut W) ∈ L ⊔ K →
      (r p)⁻¹ * (r q) ∈ S := by
    intro p q hpq
    have hd : p⁻¹ * q ∈ (L ⊔ K).subgroupOf A := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hpq
    have hr : r (p⁻¹ * q) ∈ ((L ⊔ K).subgroupOf A).map r := Subgroup.mem_map_of_mem r hd
    rw [hmapLK] at hr
    simpa [map_mul, map_inv] using hr
  have hprop : ∀ x y z : ↥R, x⁻¹ * y ∈ SR ∨ x⁻¹ * z ∈ SR ∨ y⁻¹ * z ∈ SR := by
    intro x y z
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 z.2
    rcases h.index_kBar_le_two h7 a.2 b.2 c.2 with hmem | hmem | hmem
    · left
      change ((x⁻¹ * y : ↥R) : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) ∈ S
      show x.1⁻¹ * y.1 ∈ S
      rw [← ha, ← hb]
      exact hkey a b hmem
    · right; left
      change ((x⁻¹ * z : ↥R) : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) ∈ S
      show x.1⁻¹ * z.1 ∈ S
      rw [← ha, ← hc]
      exact hkey a c hmem
    · right; right
      change ((y⁻¹ * z : ↥R) : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) ∈ S
      show y.1⁻¹ * z.1 ∈ S
      rw [← hb, ← hc]
      exact hkey b c hmem
  have htrans : ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 →
      ∃ k ∈ R, (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec u = v := by
    intro u v hu hv
    obtain ⟨a, ha⟩ := hrtrans u v hu hv
    exact ⟨r a, MonoidHom.mem_range.2 ⟨a, rfl⟩, ha⟩
  have hSRtop : SR = ⊤ := s16t3_gl3_index_two htrans hprop
  have hS : S = R := by
    have h1 : SR.map R.subtype = S := by
      change ((S.subgroupOf R).map R.subtype) = S
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSleR]
    calc S = SR.map R.subtype := h1.symm
      _ = (⊤ : Subgroup ↥R).map R.subtype := by rw [hSRtop]
      _ = R.subtype.range := Subgroup.map_top R.subtype
      _ = R := Subgroup.range_subtype R
  have hN'K' : r.ker ⊔ K' = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : r x ∈ S := by
      rw [hS]
      exact MonoidHom.mem_range.2 ⟨x, rfl⟩
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 hx
    have hmem : k⁻¹ * x ∈ r.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
    have hx2 : x = k * (k⁻¹ * x) := by group
    rw [hx2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left hmem)
  have hNsupK : N ⊔ K = A := by
    have hmap : (r.ker ⊔ K').map A.subtype = N ⊔ K := by
      rw [Subgroup.map_sup, hK'map]
    rw [hN'K', Subgroup.map_top, Subgroup.range_subtype] at hmap
    exact hmap.symm
  let φ : K' →* ↥R :=
    { toFun := fun k => ⟨r (k : ↥A), MonoidHom.mem_range.2 ⟨(k : ↥A), rfl⟩⟩
      map_one' := Subtype.ext (map_one r)
      map_mul' := fun a b => Subtype.ext (map_mul r (a : ↥A) (b : ↥A)) }
  have hφinj : Function.Injective φ := by
    intro a b hab
    have hrab : r (a : ↥A) = r (b : ↥A) :=
      congrArg (fun x : ↥R => (x : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) hab
    have hker : (a : ↥A) * (b : ↥A)⁻¹ ∈ r.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrab, mul_inv_cancel]
    have hmemK : (a : ↥A) * (b : ↥A)⁻¹ ∈ K' := K'.mul_mem a.2 (K'.inv_mem b.2)
    have hbot : (a : ↥A) * (b : ↥A)⁻¹ ∈ (⊥ : Subgroup ↥A) := by
      rw [← hkerK']
      exact ⟨hker, hmemK⟩
    have hone : (a : ↥A) * (b : ↥A)⁻¹ = 1 := by simpa using hbot
    exact Subtype.ext (mul_inv_eq_one.mp hone)
  have hφsurj : Function.Surjective φ := by
    intro y
    have hy : y.1 ∈ S := by
      rw [hS]
      exact y.2
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨k, hk⟩, Subtype.ext hky⟩
  have hcardK' : Nat.card K' = Nat.card R :=
    Nat.card_congr (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).toEquiv
  have hcardK : Nat.card K = Nat.card K' := by
    rw [← hK'map]
    exact Subgroup.card_subtype A K'
  refine ⟨N, hNle, hLleN, hNfix, hcommNK, hNK, hNsupK, ?_⟩
  rcases s16t3_gl3_transitive_card R htrans with hR7 | hR21 | hRtop
  · left
    show Nat.card K = 7
    rw [hcardK, hcardK', hR7]
  · right; left
    show Nat.card K = 21
    rw [hcardK, hcardK', hR21]
  · right; right
    haveI : IsSimpleGroup ↥R := by
      rw [hRtop]
      exact (Subgroup.topEquiv (G := Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))).isSimpleGroup
    haveI : IsSimpleGroup ↥K' := (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).isSimpleGroup
    refine ⟨?_, ?_⟩
    · show Nat.card K = 168
      rw [hcardK, hcardK']
      rw [hRtop, Subgroup.card_top, CFSG.ComponentClassification.GHarris.card_GL32_gh]
    · show IsSimpleGroup ↥K
      haveI : IsSimpleGroup ↥K := by
        rw [← hK'map]
        exact (Subgroup.equivMapOfInjective K' A.subtype A.subtype_injective).symm.isSimpleGroup
      exact ‹IsSimpleGroup ↥K›

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
