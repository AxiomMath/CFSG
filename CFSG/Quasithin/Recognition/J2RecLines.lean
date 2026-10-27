module

public import CFSG.Quasithin.Recognition.J2RecLocal

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits QuaternionGroup DihedralGroup

private abbrev QD := QuaternionGroup 2 × DihedralGroup 4

private def kapQD : QD := (QuaternionGroup.a 2, DihedralGroup.r 2)

private def zetQD : QD := (QuaternionGroup.a 2, 1)

private def zet'QD : QD := (1, DihedralGroup.r 2)

private def S0QD : Finset QD :=
  Finset.univ.filter fun m => (m * m = 1 ∨ m * m = kapQD) ∧ m ≠ 1 ∧ m ≠ kapQD ∧ m ≠ zetQD ∧
    m ≠ zet'QD

private theorem card_S0QD : S0QD.card = 20 := by decide +kernel

private theorem S0QD_mul_kap : ∀ m ∈ S0QD, m * kapQD ∈ S0QD := by decide +kernel

private theorem every_prod_QD : ∀ m : QD, ∃ s1 s2 : QD, (s1 * s1 = 1 ∨ s1 * s1 = kapQD) ∧
    (s2 * s2 = 1 ∨ s2 * s2 = kapQD) ∧ m = s1 * s2 := by decide +kernel

private theorem card_QD : Nat.card QD = 64 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide +kernel

private theorem kapQD_ne : kapQD ≠ 1 := by decide +kernel

private theorem zetQD_sq : zetQD * zetQD = 1 := by decide +kernel

private theorem zetQD_mul : zetQD * zet'QD = kapQD := by decide +kernel

private theorem ker_eq_QD {P : Type*} [Group P] [Finite P] (hP : Nat.card P = 32) (φ : QD →* P)
    (hsurj : Function.Surjective φ) (hκ : φ kapQD = 1) : ∀ k ∈ φ.ker, k = 1 ∨ k = kapQD := by
  have h := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [card_QD, hP] at h
  have hker : Nat.card φ.ker = 2 := by omega
  have hsub : ({1, kapQD} : Set QD) ⊆ (φ.ker : Set QD) := by
    intro k hk
    rcases hk with rfl | rfl
    · exact φ.ker.one_mem
    · exact hκ
  have hcard : (({1, kapQD} : Set QD)).ncard = 2 := by
    rw [Set.ncard_pair (Ne.symm kapQD_ne)]
  have hfin : (φ.ker : Set QD).Finite := Set.toFinite _
  have heq := Set.eq_of_subset_of_ncard_le hsub (by
    rw [hcard]
    have : (φ.ker : Set QD).ncard = Nat.card φ.ker := (Nat.card_coe_set_eq (φ.ker : Set QD)).symm
    rw [this, hker]) hfin
  intro k hk
  have : k ∈ ({1, kapQD} : Set QD) := by rw [heq]; exact hk
  simpa using this

theorem IsQ8D8.eq_line_of_involution {P : Type*} [Group P] (h : IsQ8D8 P) {z : P}
    (hz : z ∈ Subgroup.center P) (hz1 : z ≠ 1) {x : Fin 5 → P} (hx2 : ∀ i, x i * x i = 1)
    (hxx : ∀ i j, i ≠ j → (x i * x j) ^ 2 = z) {y : P} (hy : y * y = 1) (hy1 : y ≠ 1)
    (hyz : y ≠ z) : ∃ i, y = x i ∨ y = z * x i := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [h.1]; norm_num)
  classical
  let _ : Fintype P := Fintype.ofFinite P
  obtain ⟨φ, hsurj, hφeq, hφne, hcenter⟩ := h.exists_hom
  have hzφ : z = φ zetQD := (hcenter z hz).resolve_left hz1
  have hzc : ∀ g : P, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hz g
  have hzz : z * z = 1 := by
    rw [hzφ, ← map_mul, zetQD_sq, map_one]
  have hφζ' : φ zet'QD = z := by rw [hzφ]; exact hφeq.symm
  have hκ : φ kapQD = 1 := by
    rw [← zetQD_mul, map_mul, hφζ', ← hzφ, hzz]
  have hker := ker_eq_QD h.1 φ hsurj hκ
  set T : Finset P := Finset.univ.filter (fun y => y * y = 1 ∧ y ≠ 1 ∧ y ≠ z) with hT
  set σ : P → QD := Function.surjInv hsurj with hσ
  have hσφ : ∀ y, φ (σ y) = y := Function.surjInv_eq hsurj
  let F : P × Bool → QD := fun p => σ p.1 * (if p.2 then kapQD else 1)
  have hφF : ∀ p, φ (F p) = p.1 := by
    intro p
    simp only [F, map_mul, hσφ]
    split_ifs
    · rw [hκ, mul_one]
    · rw [map_one, mul_one]
  have hFmem : ∀ p ∈ T ×ˢ (Finset.univ : Finset Bool), F p ∈ S0QD := by
    rintro ⟨y, b⟩ hp
    simp only [Finset.mem_product, hT, Finset.mem_filter, Finset.mem_univ, true_and,
      and_true] at hp
    obtain ⟨hy2, hy1', hyz'⟩ := hp
    have hm : σ y ∈ S0QD := by
      have hmm : φ (σ y * σ y) = 1 := by rw [map_mul, hσφ, hy2]
      have hk := hker _ (MonoidHom.mem_ker.mpr hmm)
      simp only [S0QD, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hk, ?_, ?_, ?_, ?_⟩
      · intro h1; apply hy1'; rw [← hσφ y, h1, map_one]
      · intro h1; apply hy1'; rw [← hσφ y, h1, hκ]
      · intro h1; apply hyz'; rw [← hσφ y, h1, ← hzφ]
      · intro h1; apply hyz'; rw [← hσφ y, h1, hφζ']
    cases b
    · simpa [F] using hm
    · simpa [F] using S0QD_mul_kap _ hm
  have hFinj : Set.InjOn F ↑(T ×ˢ (Finset.univ : Finset Bool)) := by
    rintro ⟨y, b⟩ _ ⟨y', b'⟩ _ he
    have h1 : y = y' := by
      have e1 : φ (F (y, b)) = y := hφF (y, b)
      have e2 : φ (F (y', b')) = y' := hφF (y', b')
      rw [← e1, ← e2, he]
    subst h1
    have h2 : (if b then kapQD else 1) = (if b' then kapQD else 1) := mul_left_cancel he
    cases b <;> cases b' <;> simp_all [kapQD_ne, kapQD_ne.symm]
  have hcardle : (T ×ˢ (Finset.univ : Finset Bool)).card ≤ S0QD.card :=
    Finset.card_le_card_of_injOn F hFmem hFinj
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, card_S0QD] at hcardle
  have hTle : T.card ≤ 10 := by omega
  have hzx : ∀ w : P, (z * w) * (z * w) = w * w := by
    intro w
    calc z * w * (z * w) = z * (w * z) * w := by simp only [mul_assoc]
      _ = z * (z * w) * w := by rw [hzc w]
      _ = (z * z) * (w * w) := by simp only [mul_assoc]
      _ = w * w := by rw [hzz, one_mul]
  have hx1 : ∀ i, x i ≠ 1 ∧ x i ≠ z := by
    intro i
    obtain ⟨j, hj⟩ := exists_ne i
    have h2 := hxx i j hj.symm
    constructor
    · intro h1; rw [h1, one_mul, pow_two, hx2] at h2; exact hz1 h2.symm
    · intro h1
      rw [h1, pow_two, hzx, hx2] at h2
      exact hz1 h2.symm
  have hne : ∀ i j, i ≠ j → x i ≠ x j ∧ x i ≠ z * x j := by
    intro i j hij
    have h2 := hxx i j hij
    constructor
    · intro h1; rw [h1, pow_two, hx2, mul_one] at h2; exact hz1 h2.symm
    · intro h1
      have : x i * x j = z := by rw [h1, mul_assoc, hx2, mul_one]
      rw [this, pow_two, hzz] at h2; exact hz1 h2.symm
  let f : Fin 5 × Bool → P := fun p => if p.2 then z * x p.1 else x p.1
  have hfT : ∀ p, f p ∈ T := by
    rintro ⟨i, b⟩
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, f]
    cases b
    · exact ⟨hx2 i, (hx1 i).1, (hx1 i).2⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp only [↓reduceIte]
        rw [hzx, hx2]
      · simp only [↓reduceIte]
        intro h1
        apply (hx1 i).2
        have : x i = z⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]; exact (inv_eq_of_mul_eq_one_right hzz)
      · simp only [↓reduceIte]
        intro h1
        apply (hx1 i).1
        simpa using h1
  have hfinj : Function.Injective f := by
    rintro ⟨i, b⟩ ⟨j, b'⟩ he
    by_cases hij : i = j
    · subst hij
      cases b <;> cases b' <;> simp only [f, ↓reduceIte, Bool.false_eq_true] at he ⊢
      · exact absurd (by simpa using he.symm) hz1
      · exact absurd (by simpa using he) hz1
    · exfalso
      cases b <;> cases b' <;> simp only [f, ↓reduceIte, Bool.false_eq_true] at he
      · exact (hne i j hij).1 he
      · exact (hne i j hij).2 he
      · exact (hne j i (Ne.symm hij)).2 he.symm
      · exact (hne i j hij).1 (mul_left_cancel he)
  have himg : (Finset.univ.image f).card = 10 := by
    rw [Finset.card_image_of_injective _ hfinj]; simp
  have hsub : Finset.univ.image f ⊆ T := by
    intro t ht
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ht
    exact hfT p
  have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hyT : y ∈ T := by simp [hT, hy, hy1, hyz]
  rw [← heq] at hyT
  obtain ⟨⟨i, b⟩, -, hib⟩ := Finset.mem_image.mp hyT
  refine ⟨i, ?_⟩
  cases b
  · left; simpa [f] using hib.symm
  · right; simpa [f] using hib.symm

theorem IsQ8D8.closure_lines_eq_top {P : Type*} [Group P] (h : IsQ8D8 P) {z : P}
    (hz : z ∈ Subgroup.center P) (hz1 : z ≠ 1) {x : Fin 5 → P} (hx2 : ∀ i, x i * x i = 1)
    (hxx : ∀ i j, i ≠ j → (x i * x j) ^ 2 = z) : Subgroup.closure (Set.range x) = ⊤ := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [h.1]; norm_num)
  obtain ⟨φ, hsurj, hφeq, hφne, hcenter⟩ := h.exists_hom
  have hzφ : z = φ zetQD := (hcenter z hz).resolve_left hz1
  have hzz : z * z = 1 := by
    rw [hzφ, ← map_mul, zetQD_sq, map_one]
  have hφζ' : φ zet'QD = z := by rw [hzφ]; exact hφeq.symm
  have hκ : φ kapQD = 1 := by
    rw [← zetQD_mul, map_mul, hφζ', ← hzφ, hzz]
  set R := Subgroup.closure (Set.range x) with hR
  have hzR : z ∈ R := by
    rw [← hxx 0 1 (by decide), pow_two]
    exact R.mul_mem (R.mul_mem (Subgroup.subset_closure ⟨0, rfl⟩) (Subgroup.subset_closure ⟨1, rfl⟩))
      (R.mul_mem (Subgroup.subset_closure ⟨0, rfl⟩) (Subgroup.subset_closure ⟨1, rfl⟩))
  have hinv : ∀ t : P, t * t = 1 → t ∈ R := by
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]; exact R.one_mem
    by_cases htz : t = z
    · rw [htz]; exact hzR
    obtain ⟨i, hi | hi⟩ := IsQ8D8.eq_line_of_involution h hz hz1 hx2 hxx ht ht1 htz
    · rw [hi]; exact Subgroup.subset_closure ⟨i, rfl⟩
    · rw [hi]; exact R.mul_mem hzR (Subgroup.subset_closure ⟨i, rfl⟩)
  have hsq : ∀ s : QD, (s * s = 1 ∨ s * s = kapQD) → φ s * φ s ∈ ({1} : Set P) := by
    intro s hs
    rw [← map_mul]
    rcases hs with hs | hs <;> rw [hs]
    · simp
    · simpa using hκ
  rw [eq_top_iff]
  intro q _
  obtain ⟨m, rfl⟩ := hsurj q
  obtain ⟨s1, s2, h1, h2, rfl⟩ := every_prod_QD m
  rw [map_mul]
  exact R.mul_mem (hinv _ (by simpa using hsq s1 h1)) (hinv _ (by simpa using hsq s2 h2))

namespace IsTypeH2

variable {G : Type} [Group G] {z : G}

private theorem z_mem_center_pCoreOf (h : IsTypeH2 G z) :
    (⟨z, h.z_mem_pCoreOf⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) ∈
      Subgroup.center ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) := by
  refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
  exact Subgroup.mem_centralizer_singleton_iff.mp (pCoreOf_le 2 _ g.2)

theorem eq_line_of_involution (h : IsTypeH2 G z) {x : Fin 5 → G}
    (hxQ : ∀ i, x i ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hx : J2FiveLines z x)
    {y : G} (hyQ : y ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hy : y * y = 1)
    (hy1 : y ≠ 1) (hyz : y ≠ z) : ∃ i, y = x i ∨ y = z * x i := by
  have hz1 : (⟨z, h.z_mem_pCoreOf⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) ≠ 1 :=
    fun h1 => h.ne_one (congrArg Subtype.val h1)
  obtain ⟨i, hi⟩ := IsQ8D8.eq_line_of_involution h.q8d8 h.z_mem_center_pCoreOf hz1
    (x := fun i => ⟨x i, hxQ i⟩) (fun i => Subtype.ext (hx.x_sq i))
    (fun i j hij => Subtype.ext (by simpa using hx.sq_eq i j hij)) (y := ⟨y, hyQ⟩)
    (Subtype.ext hy) (fun h1 => hy1 (congrArg Subtype.val h1))
    (fun h1 => hyz (congrArg Subtype.val h1))
  exact ⟨i, hi.imp (congrArg Subtype.val) (congrArg Subtype.val)⟩

theorem closure_eq_pCoreOf (h : IsTypeH2 G z) {x : Fin 5 → G}
    (hxQ : ∀ i, x i ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) (hx : J2FiveLines z x) :
    Subgroup.closure (Set.range x) = pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  have hz1 : (⟨z, h.z_mem_pCoreOf⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) ≠ 1 :=
    fun h1 => h.ne_one (congrArg Subtype.val h1)
  have hcl := IsQ8D8.closure_lines_eq_top h.q8d8 h.z_mem_center_pCoreOf hz1
    (x := fun i => ⟨x i, hxQ i⟩) (fun i => Subtype.ext (hx.x_sq i))
    (fun i j hij => Subtype.ext (by simpa using hx.sq_eq i j hij))
  set Q := pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) with hQ
  have hrange : Set.range x = Q.subtype '' Set.range (fun i => (⟨x i, hxQ i⟩ : ↥Q)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨⟨x i, hxQ i⟩, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
  rw [hrange, ← MonoidHom.map_closure, hcl, Subgroup.map_top, Subgroup.range_subtype]

theorem exists_fiveLines (h : IsTypeH2 G z) :
    ∃ x : Fin 5 → G, (∀ i, x i ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∧
      J2FiveLines z x ∧
      Subgroup.closure (Set.range x) = pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  have hfin : Finite ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) :=
    Nat.finite_of_card_ne_zero (by rw [h.card_pCoreOf]; norm_num)
  have hz1 : (⟨z, h.z_mem_pCoreOf⟩ : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) ≠ 1 :=
    fun h1 => h.ne_one (congrArg Subtype.val h1)
  obtain ⟨x', hx2, -, hxx, hprod⟩ := IsQ8D8.exists_fiveLines h.q8d8 h.z_mem_center_pCoreOf hz1
  have hxQ : ∀ i, ((x' i : ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))) : G) ∈
      pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := fun i => (x' i).2
  have hx : J2FiveLines z (fun i => (x' i : G)) :=
    { d_sq := by rw [← pow_two]; exact h.sq
      x_sq := fun i => by simpa using congrArg Subtype.val (hx2 i)
      d_comm := fun i => (Subgroup.mem_centralizer_singleton_iff.mp
        (pCoreOf_le 2 _ (x' i).2)).symm
      sq_eq := fun i j hij => by simpa using congrArg Subtype.val (hxx i j hij)
      prod_eq := by simpa using congrArg Subtype.val hprod }
  exact ⟨fun i => (x' i : G), hxQ, hx, h.closure_eq_pCoreOf hxQ hx⟩

end IsTypeH2

namespace J2FiveLines

variable {G : Type*} [Group G] {d : G} {x : Fin 5 → G}

theorem x_ne_one (h : J2FiveLines d x) (hd : d ≠ 1) (i : Fin 5) : x i ≠ 1 := by
  obtain ⟨j, hj⟩ := exists_ne i
  intro h1
  have h2 := h.sq_eq i j hj.symm
  rw [h1, one_mul, pow_two, h.x_sq] at h2
  exact hd h2.symm

theorem x_ne_d (h : J2FiveLines d x) (hd : d ≠ 1) (i : Fin 5) : x i ≠ d := by
  obtain ⟨j, hj⟩ := exists_ne i
  intro h1
  have h2 := h.sq_eq i j hj.symm
  have h3 : (d * x j) * (d * x j) = 1 := by
    calc d * x j * (d * x j) = d * (x j * d) * x j := by simp only [mul_assoc]
      _ = d * (d * x j) * x j := by rw [(h.d_comm j).eq]
      _ = (d * d) * (x j * x j) := by simp only [mul_assoc]
      _ = 1 := by rw [h.d_sq, h.x_sq, one_mul]
  rw [h1, pow_two, h3] at h2
  exact hd h2.symm

theorem x_ne_x (h : J2FiveLines d x) (hd : d ≠ 1) {i j : Fin 5} (hij : i ≠ j) : x i ≠ x j := by
  intro h1
  have h2 := h.sq_eq i j hij
  rw [h1, pow_two, h.x_sq, mul_one] at h2
  exact hd h2.symm

theorem x_ne_dx (h : J2FiveLines d x) (hd : d ≠ 1) {i j : Fin 5} (hij : i ≠ j) :
    x i ≠ d * x j := by
  intro h1
  have h2 := h.sq_eq i j hij
  have : x i * x j = d := by rw [h1, mul_assoc, h.x_sq, mul_one]
  rw [this, pow_two, h.d_sq] at h2
  exact hd h2.symm

end J2FiveLines

end CFSG.Quasithin
