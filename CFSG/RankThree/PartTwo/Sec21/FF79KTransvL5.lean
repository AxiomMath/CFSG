module

public import CFSG.RankThree.PartTwo.Sec21.FF79KAutL5
public import CFSG.GroupTheory.GL52.OrderThree
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.GroupTheory.GL52 Matrix
open scoped Pointwise

@[expose] def qM (c a1 a2 a3 w1 w2 w3 : ZMod 2) : M5 :=
  !![1, a1, a2, a3, c; 0, 1, 0, 0, w1; 0, 0, 1, 0, w2; 0, 0, 0, 1, w3; 0, 0, 0, 0, 1]

private theorem qM_comm (c a1 a2 a3 w1 w2 w3 c' a1' a2' a3' w1' w2' w3' : ZMod 2) :
    qM c a1 a2 a3 w1 w2 w3 * qM c' a1' a2' a3' w1' w2' w3' =
        qM c' a1' a2' a3' w1' w2' w3' * qM c a1 a2 a3 w1 w2 w3 ∨
      qM c a1 a2 a3 w1 w2 w3 * qM c' a1' a2' a3' w1' w2' w3' =
        invT0M * (qM c' a1' a2' a3' w1' w2' w3' * qM c a1 a2 a3 w1 w2 w3) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  by_cases hd : a1 * w1' + a2 * w2' + a3 * w3' + a1' * w1 + a2' * w2 + a3' * w3 = 0
  · left
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qM, invT0M, Matrix.mul_apply, Fin.sum_univ_five] <;>
      first | ring1 | (rw [← CharTwo.add_eq_zero]; ring_nf; reduce_mod_char; linear_combination hd)
  · right
    have hd1 := key _ hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qM, invT0M, Matrix.mul_apply, Fin.sum_univ_five] <;>
      first | ring1 | (rw [← CharTwo.add_eq_zero]; ring_nf; reduce_mod_char; first | linear_combination hd1 | linear_combination hd1 + h2)

@[expose] noncomputable def piHom :
    (Subgroup.centralizer {invT0} : Subgroup G52) →* GL (Fin 3) (ZMod 2) where
  toFun g := invMidUnit g.2
  map_one' := Units.ext (by
    show invMid (((1 : Subgroup.centralizer {invT0}) : G52) : M5) = 1
    rw [Subgroup.coe_one, Units.val_one, invMid_one])
  map_mul' x y := Units.ext (by
    show invMid ((((x * y : Subgroup.centralizer {invT0})) : G52) : M5) =
      invMid ((x : G52) : M5) * invMid ((y : G52) : M5)
    rw [Subgroup.coe_mul, Units.val_mul]
    exact invMid_mul (inv_t0_shape x.2).1 (inv_t0_shape y.2).2.1)

theorem piHom_surjective : Function.Surjective piHom := by
  intro B
  have hmem : invLinHom B ∈ Subgroup.centralizer {invT0} := by
    have : invAHom (SemidirectProduct.inr B) = invLinHom B := SemidirectProduct.lift_inr _ _ _ _
    rw [← this]
    exact inv_A_le ⟨_, rfl⟩
  refine ⟨⟨invLinHom B, hmem⟩, Units.ext ?_⟩
  show invMid ((invLinHom B : G52) : M5) = (B : Matrix (Fin 3) (Fin 3) (ZMod 2))
  rw [invLinHom]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, coe_mk5]
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem mid_eq_one {R : Subgroup G52} (hp : IsPGroup 2 R)
    (hRC : R ≤ Subgroup.centralizer {invT0})
    (hn : ∀ g ∈ Subgroup.centralizer {invT0}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    ∀ r ∈ R, invMid ((r : G52) : M5) = 1 := by
  let C : Subgroup G52 := Subgroup.centralizer {invT0}
  let R' : Subgroup C := R.subgroupOf C
  haveI : R'.Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hn g g.2 x hx⟩
  have hp' : IsPGroup 2 R' := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hRC).symm
  haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  haveI hnormal : (R'.map piHom).Normal := Subgroup.Normal.map inferInstance piHom piHom_surjective
  have h2 : IsPGroup 2 (R'.map piHom) := hp'.map piHom
  intro r hr
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R'.map piHom) with hbot | htop
  · have hmem : piHom ⟨r, hRC hr⟩ ∈ R'.map piHom :=
      ⟨⟨r, hRC hr⟩, Subgroup.mem_subgroupOf.2 hr, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg (fun B : GL (Fin 3) (ZMod 2) => (B : Matrix (Fin 3) (Fin 3) (ZMod 2))) hmem
  · exfalso
    rw [htop] at h2
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
    rw [Subgroup.card_top, CFSG.ComponentClassification.GHarris.card_GL32_gh] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 168)
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega

theorem shape_eq {g : G52} (hg : g ∈ Subgroup.centralizer {invT0})
    (hm : invMid (g : M5) = 1) :
    (g : M5) = qM ((g : M5) 0 4) ((g : M5) 0 1) ((g : M5) 0 2) ((g : M5) 0 3) ((g : M5) 1 4)
      ((g : M5) 2 4) ((g : M5) 3 4) := by
  obtain ⟨hcol, hrow, h00, h44⟩ := inv_t0_shape hg
  have c1 := hcol 1 (by decide)
  have c2 := hcol 2 (by decide)
  have c3 := hcol 3 (by decide)
  have c4 := hcol 4 (by decide)
  have r0 := hrow 0 (by decide)
  have r1 := hrow 1 (by decide)
  have r2 := hrow 2 (by decide)
  have r3 := hrow 3 (by decide)
  have m : ∀ a b : Fin 3, (g : M5) a.succ.castSucc b.succ.castSucc = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) a b := by
    intro a b
    have := congrFun (congrFun hm a) b
    simpa [invMid] using this
  have m00 := m 0 0
  have m01 := m 0 1
  have m02 := m 0 2
  have m10 := m 1 0
  have m11 := m 1 1
  have m12 := m 1 2
  have m20 := m 2 0
  have m21 := m 2 1
  have m22 := m 2 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all [qM, Matrix.one_apply]

theorem comm_mem_t0 {g h : G52} (hg : g ∈ Subgroup.centralizer {invT0})
    (hh : h ∈ Subgroup.centralizer {invT0}) (hmg : invMid (g : M5) = 1)
    (hmh : invMid (h : M5) = 1) : g * h * g⁻¹ * h⁻¹ ∈ Subgroup.zpowers invT0 := by
  have e : g * h * g⁻¹ * h⁻¹ = (g * h) * (h * g)⁻¹ := by group
  rw [e]
  rcases qM_comm ((g : M5) 0 4) ((g : M5) 0 1) ((g : M5) 0 2) ((g : M5) 0 3) ((g : M5) 1 4)
      ((g : M5) 2 4) ((g : M5) 3 4) ((h : M5) 0 4) ((h : M5) 0 1) ((h : M5) 0 2) ((h : M5) 0 3)
      ((h : M5) 1 4) ((h : M5) 2 4) ((h : M5) 3 4) with H | H
  · rw [← shape_eq hg hmg, ← shape_eq hh hmh] at H
    have : g * h = h * g := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact H)
    rw [this, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [← shape_eq hg hmg, ← shape_eq hh hmh] at H
    have : g * h = invT0 * (h * g) :=
      Units.ext (by rw [Units.val_mul, Units.val_mul, Units.val_mul]; exact H)
    rw [this, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers _

private theorem transv_normal2 {s : G52} (hs : s ^ 2 = 1) (h1 : commDim s = 1)
    (R : Subgroup G52) (hp : IsPGroup 2 R) (hRC : R ≤ Subgroup.centralizer {s})
    (hn : ∀ g ∈ Subgroup.centralizer {s}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ Subgroup.zpowers s := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (inv_isConj_t0 hs h1)
  set f : G52 →* G52 := (MulAut.conj c⁻¹).toMonoidHom with hf
  have hfx : ∀ x, f x = c⁻¹ * x * c := fun x => by simp [hf, MulAut.conj_apply]
  have hinj : Function.Injective f := (MulAut.conj c⁻¹).injective
  have hscomm : ∀ x, x ∈ Subgroup.centralizer {s} → f x ∈ Subgroup.centralizer {invT0} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    rw [hfx]
    have : invT0 = c⁻¹ * s * c := by rw [← hc]; group
    rw [this]
    calc c⁻¹ * x * c * (c⁻¹ * s * c) = c⁻¹ * (x * s) * c := by group
      _ = c⁻¹ * (s * x) * c := by rw [hx]
      _ = c⁻¹ * s * c * (c⁻¹ * x * c) := by group
  have hR' : R.map f ≤ Subgroup.centralizer {invT0} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hscomm x (hRC hx)
  have hp' : IsPGroup 2 (R.map f) := hp.of_equiv (Subgroup.equivMapOfInjective R f hinj)
  have hn' : ∀ g ∈ Subgroup.centralizer {invT0}, ∀ r ∈ R.map f, g * r * g⁻¹ ∈ R.map f := by
    rintro g hg _ ⟨x, hx, rfl⟩
    have hg' : c * g * c⁻¹ ∈ Subgroup.centralizer {s} := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      have : s = c * invT0 * c⁻¹ := hc.symm
      rw [this]
      calc c * g * c⁻¹ * (c * invT0 * c⁻¹) = c * (g * invT0) * c⁻¹ := by group
        _ = c * (invT0 * g) * c⁻¹ := by rw [hg]
        _ = c * invT0 * c⁻¹ * (c * g * c⁻¹) := by group
    refine ⟨(c * g * c⁻¹) * x * (c * g * c⁻¹)⁻¹, hn _ hg' x hx, ?_⟩
    rw [hfx, hfx]
    group
  have hmid := mid_eq_one hp' hR' hn'
  intro r₁ hr₁ r₂ hr₂
  have hx1 : f r₁ ∈ R.map f := ⟨r₁, hr₁, rfl⟩
  have hx2 : f r₂ ∈ R.map f := ⟨r₂, hr₂, rfl⟩
  have key := comm_mem_t0 (hR' hx1) (hR' hx2) (hmid _ hx1) (hmid _ hx2)
  have hcs : s = c * invT0 * c⁻¹ := hc.symm
  have : r₁ * r₂ * r₁⁻¹ * r₂⁻¹ = c * (f r₁ * f r₂ * (f r₁)⁻¹ * (f r₂)⁻¹) * c⁻¹ := by
    rw [hfx, hfx]; group
  rw [this]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 key
  rw [← hk, hcs]
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  exact conj_zpow

private theorem commDim_le_one {x : G52}
    (h : ∃ j0 : Fin 5, ∀ c : Fin 5, (fun r => ((x : M5) - 1) r c) = 0 ∨
      (fun r => ((x : M5) - 1) r c) = (fun r => ((x : M5) - 1) r j0)) : commDim x ≤ 1 := by
  obtain ⟨j0, hj0⟩ := h
  set w : V5 := fun r => ((x : M5) - 1) r j0 with hw
  set N : M5 := (x : M5) - 1 with hN
  have hr : LinearMap.range (toLin' N) ≤ Submodule.span (ZMod 2) {w} := by
    rintro _ ⟨v, rfl⟩
    rw [Submodule.mem_span_singleton]
    classical
    let t : Fin 5 → ZMod 2 := fun c => if (fun r => N r c) = 0 then 0 else 1
    have ht : ∀ r c, N r c = t c * w r := by
      intro r c
      rcases hj0 c with h | h
      · have : N r c = 0 := congrFun h r
        simp [t, h, this]
      · have hne : (fun r => N r c) ≠ 0 ∨ (fun r => N r c) = 0 := by tauto
        by_cases h0 : (fun r => N r c) = 0
        · have : N r c = 0 := congrFun h0 r
          simp [t, h0, this]
        · simp only [t, h0, if_false, one_mul]
          exact congrFun h r
    refine ⟨∑ c, t c * v c, ?_⟩
    ext r
    simp only [toLin'_apply, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ht r c]
    ring
  calc commDim x = Module.finrank (ZMod 2) (LinearMap.range (toLin' N)) := rfl
    _ ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {w}) := Submodule.finrank_mono hr
    _ ≤ 1 := by
      refine (finrank_span_le_card ({w} : Set V5)).trans ?_
      simp

private local instance : DecidableEq (Equiv.Perm (Fin 3)) :=
  Fintype.decidableEqEquivFintype

private theorem trace_zero_of_seven {y : G52} (hy : orderOf y = 3)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer ({y} : Set G52))) : Matrix.trace (y : M5) = 0 := by
  rcases ord3_structure hy with ⟨h4, K, ⟨hsup, hinf, hcomm⟩, ⟨e⟩⟩ | ⟨h2, -⟩
  · exfalso
    have hA : Subgroup.zpowers y ≤ Subgroup.normalizer (K : Set G52) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have := hcomm g hg x hx
        rwa [this, mul_inv_cancel_right]
      · intro hx
        have h1 := hcomm g⁻¹ (inv_mem hg) _ hx
        have : x = g * x * g⁻¹ := by
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = (g * x * g⁻¹) * g⁻¹ * g := by rw [h1]
            _ = g * x * g⁻¹ := by group
        rw [this]
        exact hx
    have hcard : Nat.card (Subgroup.centralizer ({y} : Set G52)) = 60 * 3 := by
      rw [← hsup, sup_comm, inv_card_sup hA (by rw [inf_comm]; exact hinf), Nat.card_zpowers, hy,
        Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    rw [hcard] at h7
    omega
  · rcases ord3_classify hy with ⟨-, hc⟩ | ⟨h4, -⟩
    · obtain ⟨c, hc⟩ := isConj_iff.1 hc
      rw [← hc]
      have := syl3_trace_conj c ord3T2M
      simpa [ord3T2, syl3_trace_ab.1] using this
    · omega

set_option maxRecDepth 100000 in
private theorem finite_check : ∀ i j : Fin 3, ((i : ℕ) = 0 ↔ (j : ℕ) ≠ 0) →
    ∀ m n : Fin 3, ∀ x : DihedralGroup 4,
    ord3T2M ^ (m : ℕ) * syl3TbM ^ (n : ℕ) * syl3DM x *
      (ord3T2M ^ (m : ℕ) * syl3TbM ^ (n : ℕ) * syl3DM x) = 1 →
    ord3T2M ^ (m : ℕ) * syl3TbM ^ (n : ℕ) * syl3DM x * (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) =
      (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) * (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) *
        (ord3T2M ^ (m : ℕ) * syl3TbM ^ (n : ℕ) * syl3DM x) →
    ∀ k l : Fin 3,
    ord3T2M ^ (m : ℕ) * syl3TbM ^ (n : ℕ) * syl3DM x * (ord3T2M ^ (k : ℕ) * syl3TbM ^ (l : ℕ)) =
      (ord3T2M ^ (k : ℕ) * syl3TbM ^ (l : ℕ)) *
        (ord3T2M ^ (m : ℕ) * syl3TbM ^ (n : ℕ) * syl3DM x) →
    ord3T2M ^ (k : ℕ) * syl3TbM ^ (l : ℕ) ≠ 1 →
    ord3T2M ^ (k : ℕ) * syl3TbM ^ (l : ℕ) ≠ ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ) →
    ord3T2M ^ (k : ℕ) * syl3TbM ^ (l : ℕ) ≠
      (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) * (ord3T2M ^ (i : ℕ) * syl3TbM ^ (j : ℕ)) →
    ∃ j0 : Fin 5, ∀ c : Fin 5,
      (fun r => (ord3T2M ^ (m : ℕ) * syl3TbM ^ (n : ℕ) * syl3DM x - 1) r c) = 0 ∨
      (fun r => (ord3T2M ^ (m : ℕ) * syl3TbM ^ (n : ℕ) * syl3DM x - 1) r c) =
        (fun r => (ord3T2M ^ (m : ℕ) * syl3TbM ^ (n : ℕ) * syl3DM x - 1) r j0) := by
  decide +kernel

private theorem exists_conj_normalizer {y z s : G52} (hy : orderOf y = 3) (hz : orderOf z = 3)
    (hyz : y * z = z * y) (hzy : z ∉ Subgroup.zpowers y) (hsy : s * y * s⁻¹ = y⁻¹)
    (hsz : s * z = z * s) :
    ∃ c : G52, c⁻¹ * y * c ∈ syl3R ∧ c⁻¹ * z * c ∈ syl3R ∧
      c⁻¹ * s * c ∈ Subgroup.normalizer (syl3R : Set G52) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_zpowers_sup hy hz hyz hzy
  obtain ⟨Q0, hQ0⟩ := exists_sylow_eq_of_card_pow (p := 3) (k := 2) (H := syl3R)
    (by rw [syl3_card_R]; norm_num) (fun P => by rw [syl3_card_sylow P]; norm_num)
  obtain ⟨c, hc⟩ := exists_eq_map_conj_sylow Q0 Q
  rw [hQ0] at hc
  have hyQ : y ∈ (Q : Subgroup G52) := by
    rw [hQ]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hzQ : z ∈ (Q : Subgroup G52) := by
    rw [hQ]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hsN : s ∈ Subgroup.normalizer ((Q : Subgroup G52) : Set G52) := by
    rw [hQ]
    refine syl3_mem_normalizer_of_map_le ?_
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · show s * y * s⁻¹ ∈ _
      rw [hsy]
      exact Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
    · show s * z * s⁻¹ ∈ _
      rw [hsz, mul_inv_cancel_right]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [hc] at hyQ
    obtain ⟨r, hr, hry⟩ := hyQ
    have : r = c⁻¹ * y * c := by
      rw [← hry]; simp [MulAut.conj_apply]; group
    rwa [← this]
  · rw [hc] at hzQ
    obtain ⟨r, hr, hrz⟩ := hzQ
    have : r = c⁻¹ * z * c := by
      rw [← hrz]; simp [MulAut.conj_apply]; group
    rwa [← this]
  · have hN : Subgroup.normalizer ((Q : Subgroup G52) : Set G52) =
        (Subgroup.normalizer (syl3R : Set G52)).map (MulAut.conj c).toMonoidHom := by
      rw [hc, normalizer_map_conj]
    rw [hN] at hsN
    obtain ⟨g, hg, hgs⟩ := hsN
    have : g = c⁻¹ * s * c := by
      rw [← hgs]; simp [MulAut.conj_apply]; group
    rwa [← this]

private theorem core_commDim {y' z' s' : G52} (hy : y' ∈ syl3R) (hz : z' ∈ syl3R)
    (hs : s' ∈ Subgroup.normalizer (syl3R : Set G52)) (hs2 : s' * s' = 1)
    (hsy : s' * y' = y' * y' * s') (hsz : s' * z' = z' * s') (hz1 : z' ≠ 1) (hzy : z' ≠ y')
    (hzy2 : z' ≠ y' * y') (htr : Matrix.trace (y' : M5) = 0) : commDim s' ≤ 1 := by
  obtain ⟨i, hi, j, hj, hyij⟩ := syl3_mem_R hy
  obtain ⟨k, hk, l, hl, hzkl⟩ := syl3_mem_R hz
  rw [← syl3_normalizer_eq] at hs
  have hmul : ((syl3R ⊔ syl3T : Subgroup G52) : Set G52) = (syl3R : Set G52) * (syl3T : Set G52) :=
    Subgroup.coe_mul_of_right_le_normalizer_left syl3R syl3T syl3_T_le_normalizer
  have hs' : s' ∈ (syl3R : Set G52) * (syl3T : Set G52) := by rw [← hmul]; exact hs
  obtain ⟨r, hr, t, ⟨x, rfl⟩, hrt⟩ := hs'
  obtain ⟨m, hm, n, hn, hrmn⟩ := syl3_mem_R hr
  have hSm : (s' : M5) = ord3T2M ^ m * syl3TbM ^ n * syl3DM x := by
    rw [← hrt, hrmn, Units.val_mul, Units.val_mul, syl3_pow_matrix_a, syl3_pow_matrix_b]
    rfl
  have hYm : (y' : M5) = ord3T2M ^ i * syl3TbM ^ j := by
    rw [hyij, Units.val_mul, syl3_pow_matrix_a, syl3_pow_matrix_b]
  have hZm : (z' : M5) = ord3T2M ^ k * syl3TbM ^ l := by
    rw [hzkl, Units.val_mul, syl3_pow_matrix_a, syl3_pow_matrix_b]
  have hcoe : ∀ {g h : G52}, g = h → (g : M5) = (h : M5) := fun e => by rw [e]
  have hne : ∀ {g h : G52}, g ≠ h → (g : M5) ≠ (h : M5) := fun e e' => e (Units.ext e')
  have htrace : (i = 0 ↔ j ≠ 0) := by
    have := syl3_trace ⟨i, hi⟩ ⟨j, hj⟩ (by rw [← hYm]; exact htr)
    simpa using this
  have h1 : (ord3T2M ^ m * syl3TbM ^ n * syl3DM x) * (ord3T2M ^ m * syl3TbM ^ n * syl3DM x) = 1 := by
    rw [← hSm, ← Units.val_mul, hs2, Units.val_one]
  have h2 : (ord3T2M ^ m * syl3TbM ^ n * syl3DM x) * (ord3T2M ^ i * syl3TbM ^ j) =
      (ord3T2M ^ i * syl3TbM ^ j) * (ord3T2M ^ i * syl3TbM ^ j) *
        (ord3T2M ^ m * syl3TbM ^ n * syl3DM x) := by
    rw [← hSm, ← hYm, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hsy]
  have h3 : (ord3T2M ^ m * syl3TbM ^ n * syl3DM x) * (ord3T2M ^ k * syl3TbM ^ l) =
      (ord3T2M ^ k * syl3TbM ^ l) * (ord3T2M ^ m * syl3TbM ^ n * syl3DM x) := by
    rw [← hSm, ← hZm, ← Units.val_mul, ← Units.val_mul, hsz]
  have h4 : ord3T2M ^ k * syl3TbM ^ l ≠ 1 := by
    rw [← hZm]; exact fun h => hz1 (Units.ext (by rw [h, Units.val_one]))
  have h5 : ord3T2M ^ k * syl3TbM ^ l ≠ ord3T2M ^ i * syl3TbM ^ j := by
    rw [← hZm, ← hYm]; exact hne hzy
  have h6 : ord3T2M ^ k * syl3TbM ^ l ≠
      (ord3T2M ^ i * syl3TbM ^ j) * (ord3T2M ^ i * syl3TbM ^ j) := by
    rw [← hZm, ← hYm, ← Units.val_mul]; exact hne hzy2
  have key := finite_check ⟨i, hi⟩ ⟨j, hj⟩ htrace ⟨m, hm⟩ ⟨n, hn⟩ x h1 h2 ⟨k, hk⟩ ⟨l, hl⟩ h3 h4 h5 h6
  apply commDim_le_one
  rw [hSm]
  exact key

theorem commDim_le_one_of_data {y z s : G52} (hs : orderOf s = 2) (hy : orderOf y = 3)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer ({y} : Set G52))) (hsy : s * y * s⁻¹ = y⁻¹)
    (hz : orderOf z = 3) (hzc : z * y = y * z) (hzy : z ∉ Subgroup.zpowers y)
    (hsz : s * z = z * s) : commDim s ≤ 1 := by
  obtain ⟨c, hy', hz', hs'⟩ := exists_conj_normalizer hy hz hzc.symm hzy hsy hsz
  have hy3 : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy] at this
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs, pow_two] at this
  have hyinv : y⁻¹ = y * y := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three]
    exact hy3
  have hsy2 : s * y = y * y * s := by
    calc s * y = (s * y * s⁻¹) * s := by group
      _ = y⁻¹ * s := by rw [hsy]
      _ = y * y * s := by rw [hyinv]
  have htr : Matrix.trace ((c⁻¹ * y * c : G52) : M5) = 0 := by
    have h0 := trace_zero_of_seven hy h7
    have := syl3_trace_conj c⁻¹ (y : M5)
    rw [h0] at this
    rw [show (c⁻¹ * y * c : G52) = c⁻¹ * y * c⁻¹⁻¹ by rw [inv_inv], Units.val_mul, Units.val_mul]
    exact this
  have hcs : commDim (c⁻¹ * s * c) ≤ 1 := by
    refine core_commDim hy' hz' hs' ?_ ?_ ?_ ?_ ?_ ?_ htr
    · calc c⁻¹ * s * c * (c⁻¹ * s * c) = c⁻¹ * (s * s) * c := by group
        _ = 1 := by rw [hs2]; group
    · calc c⁻¹ * s * c * (c⁻¹ * y * c) = c⁻¹ * (s * y) * c := by group
        _ = c⁻¹ * (y * y * s) * c := by rw [hsy2]
        _ = c⁻¹ * y * c * (c⁻¹ * y * c) * (c⁻¹ * s * c) := by group
    · calc c⁻¹ * s * c * (c⁻¹ * z * c) = c⁻¹ * (s * z) * c := by group
        _ = c⁻¹ * (z * s) * c := by rw [hsz]
        _ = c⁻¹ * z * c * (c⁻¹ * s * c) := by group
    · intro h
      have : z = 1 := by
        calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
          _ = 1 := by rw [h]; group
      rw [this, orderOf_one] at hz
      omega
    · intro h
      apply hzy
      have : z = y := by
        calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
          _ = c * (c⁻¹ * y * c) * c⁻¹ := by rw [h]
          _ = y := by group
      rw [this]
      exact Subgroup.mem_zpowers y
    · intro h
      apply hzy
      have : z = y * y := by
        calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
          _ = c * (c⁻¹ * y * c * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
          _ = y * y := by group
      rw [this, ← pow_two]
      exact Subgroup.npow_mem_zpowers y 2
  have hse : s = c * (c⁻¹ * s * c) * c⁻¹ := by group
  rw [hse, commDim_conj]
  exact hcs

theorem ff79KTransvL5_holds : FF79KTransvL5 := by
  intro s y z hs hy h7 hsy hz hzc hzy hsz R hR hRC hRn
  have hs2 : s ^ 2 = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs] at this
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  have hle := commDim_le_one_of_data hs hy h7 hsy hz hzc hzy hsz
  have h1 : commDim s = 1 := by
    rcases inv_commDim_eq_one_or_two hs2 hs1 with h | h
    · exact h
    · omega
  exact transv_normal2 hs2 h1 R hR hRC hRn

end CFSG.RankThree.PartTwo.Sec21.FF79
