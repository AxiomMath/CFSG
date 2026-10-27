module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3322C

public section

namespace CFSG.Quasithin.H13.L3322

open Equiv Equiv.Perm
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique hiding evenWeight
open CFSG.Quasithin.H13.A7 (IsCoordAct vec natLam)
open CFSG.Quasithin.SteinbergCB (permAct7 evenWeight sevenP)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

section Tools

open scoped Pointwise

omit [Finite G] in
theorem map_conj_centralizer_le (g x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
    _ = g * (x * y) * g⁻¹ := by rw [hy]
    _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group

omit [Finite G] in
theorem exists_mul_of_mem_sup_comm {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hset : (B : Set G) * (A : Set G) = (A : Set G) * (B : Set G) := by
    ext y
    constructor
    · rintro ⟨b, hb, a, ha, rfl⟩
      exact ⟨a, ha, b, hb, hAB a ha b hb⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨b, hb, a, ha, (hAB a ha b hb).symm⟩
  have h1 := A4.coe_sup_eq_mul_of_mul_comm hset
  rw [← SetLike.mem_coe, h1] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨a, ha, b, hb, rfl⟩

omit [Finite G] in
theorem commute_of_sq {g x : G} (hg : Odd (orderOf g)) (h : Commute (g ^ 2) x) : Commute g x := by
  obtain ⟨k, hk⟩ := hg
  have hg' : g = (g ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hg']
  exact h.pow_left (k + 1)

omit [Finite G] in
theorem omegaOneCenter_comm (T : Subgroup G) {u v : G} (hu : u ∈ quasithinOmegaOneCenter T)
    (hv : v ∈ quasithinOmegaOneCenter T) : u * v = v * u := by
  have hZT : quasithinOmegaOneCenter T ≤ T := (Subgroup.closure_le _).2 fun x hx => hx.1.1
  exact Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T (hZT hv)) u hu

end Tools

section Unique

omit [Finite G] in
theorem pCoreOf_centralizer_ne_bot {z : G} (hz2 : orderOf z = 2) :
    pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hle : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)) ?_
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one]))
    rw [A7.normalizer_zpowers_eq_centralizer' hz2]
  intro hbot
  apply hz1
  have := hle (Subgroup.mem_zpowers z)
  rw [hbot, Subgroup.mem_bot] at this
  exact this

theorem isUniqueM_centralizer (h5 : Stmt3_3_5) (h : Hyp331 G T M L D) (hML : mPlus L T = L)
    {c : G} (hcZ : c ∈ quasithinOmegaOneCenter T) (hcL : c ∈ Subgroup.centralizer (L : Set G))
    (hc1 : c ≠ 1) : IsUniqueM (Subgroup.centralizer ({c} : Set G)) M := by
  have hc2 : orderOf c = 2 := orderOf_eq_prime (sq_eq_one_of_mem_omegaOneCenter T hcZ) hc1
  have hLT : L ⊔ T ≤ Subgroup.centralizer ({c} : Set G) := by
    refine sup_le (fun l hl => ?_) (fun t ht => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hcL l hl
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T ht) c
        hcZ).symm
  have hle := le_M h5 h hML hLT (pCoreOf_centralizer_ne_bot hc2)
  obtain ⟨-, hU, -⟩ := h5 G T M L h.toSetup331
  rw [hML] at hU
  exact ⟨⟨h.maxM, hle⟩, fun M' hM' => hU.2 M' ⟨hM'.1, hLT.trans hM'.2⟩⟩

theorem mem_M_of_conj_mem_centralizer (h5 : Stmt3_3_5) (h : Hyp331 G T M L D)
    (hML : mPlus L T = L) {c g : G} (hcZ : c ∈ quasithinOmegaOneCenter T)
    (hcL : c ∈ Subgroup.centralizer (L : Set G)) (hc1 : c ≠ 1)
    (hgZ : g * c * g⁻¹ ∈ quasithinOmegaOneCenter T)
    (hgL : g * c * g⁻¹ ∈ Subgroup.centralizer (L : Set G)) : g ∈ M := by
  have hU := isUniqueM_centralizer h5 h hML hcZ hcL hc1
  have hg1 : g * c * g⁻¹ ≠ 1 := fun h1 => hc1 (by
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hU' := isUniqueM_centralizer h5 h hML hgZ hgL hg1
  have hM' : InM (Subgroup.centralizer ({g * c * g⁻¹} : Set G))
      (M.map (MulAut.conj g).toMonoidHom) := by
    refine ⟨quasithinIsMaxTwoLocal_map_conj h.maxM g, fun x hx => ?_⟩
    rw [A38.mem_map_conj]
    apply hU.1.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g⁻¹ * x * g * c = g⁻¹ * (x * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * x) * g := by rw [hx]
      _ = c * (g⁻¹ * x * g) := by group
  have heq := hU'.2 _ hM'
  exact (normalizer_eq_of_quasithinIsMaxTwoLocal h.maxM).le
    (Subgroup.mem_normalizer_iff_map_conj_eq.2 heq)

theorem exists_mem_D_not_mem_M (h : Hyp331 G T M L D) : ∃ d ∈ D, d ∉ M := by
  by_contra hall
  push Not at hall
  exact h.counter (by rw [h.ND]; exact sup_le h.TM hall)

end Unique

section Theta

variable {ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)}

omit [Finite G] in
theorem coe_ne_one_of_vec_six {e : ↥⁅vPlus L T, L⁆} (he : vec ψ e = A7.vecSix) :
    (e : G) ≠ 1 := by
  intro h1
  have h2 : e = 1 := Subtype.ext h1
  rw [h2, A7.vec_one] at he
  exact absurd he (by decide)

theorem pCoreOf_ne_bot_of_vec_six (h : Hyp331 G T M L D) {e : ↥⁅vPlus L T, L⁆}
    (he : vec ψ e = A7.vecSix) : pCoreOf 2 (L ⊔ T) ≠ ⊥ := by
  intro hb
  have heR : (e : G) ∈ pCoreOf 2 (L ⊔ T) :=
    ((Hyp331.vPlus_reduced h.toSetup331).1 (L3317.commV_le_vPlus h e.2)).1
  rw [hb, Subgroup.mem_bot] at heR
  exact coe_ne_one_of_vec_six he heR

theorem lTheta_ne (h : Hyp331 G T M L D) (hc : Coord322 T L ψ) {e : ↥⁅vPlus L T, L⁆}
    (he : vec ψ e = A7.vecSix) : lTheta L e ≠ L := by
  intro hLθ
  have hLW := L3317.le_normalizer_commV h
  have hmap : ((lTheta L (e : G)).subgroupOf L).map (natLam hLW hc.Lact) = A7.stabA7 A7.vecSix :=
    A7.natLam_map_Le_six hLW hc.Lact hc.Lonto he
  rw [hLθ, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 (A7.natLam_surjective hLW hc.Lact hc.Lonto)] at hmap
  have hmem : (⟨swap 4 6 * swap 4 5, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩ :
      alternatingGroup (Fin 7)) ∈ A7.stabA7 A7.vecSix := hmap ▸ Subgroup.mem_top _
  rw [A7.mem_stabA7, A7.permAct7_vecSix_iff] at hmem
  exact absurd hmem (by decide)

theorem false_of_conj_eq_mul (h : Hyp331 G T M L D) (hc : Coord322 T L ψ)
    {e : ↥⁅vPlus L T, L⁆} (he : vec ψ e = A7.vecSix)
    (hθ : ∀ c ∈ quasithinOmegaOneCenter T, c ∈ Subgroup.centralizer (L : Set G) →
      thetaOf (Subgroup.centralizer ({c * (e : G)} : Set G)) ≤ lTheta L e)
    {z g c : G} (hzL : z ∈ Subgroup.centralizer (L : Set G))
    (hcZ : c ∈ quasithinOmegaOneCenter T) (hcL : c ∈ Subgroup.centralizer (L : Set G))
    (hgz : g * z * g⁻¹ = c * e) : False := by
  set f := (MulAut.conj g).toMonoidHom with hf
  have hLz : L ≤ Subgroup.centralizer ({z} : Set G) := fun l hl => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 hzL l hl
  have h1 : L.map f ≤ lTheta L e := by
    calc L.map f ≤ (thetaOf L).map f := Subgroup.map_mono (le_thetaOf_L h hc)
      _ ≤ thetaOf (L.map f) := map_thetaOf_le L f (MulAut.conj g).injective
      _ ≤ thetaOf (Subgroup.centralizer ({c * (e : G)} : Set G)) := by
          apply A7.theta_mono
          rw [← hgz]
          exact (Subgroup.map_mono hLz).trans (map_conj_centralizer_le g z)
      _ ≤ lTheta L e := hθ c hcZ hcL
  have hcard : Nat.card (L.map f) = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  apply lTheta_ne h hc he
  refine Subgroup.eq_of_le_of_card_ge (lTheta_le L _) ?_
  rw [← hcard]
  exact Subgroup.card_le_of_le h1

theorem mem_M_of_conj_eq_mul (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h14 : Stmt3_3_14)
    (h : Hyp331 G T M L D) (hc : Coord322 T L ψ) {e : ↥⁅vPlus L T, L⁆}
    (he : vec ψ e = A7.vecSix) (heZ : (e : G) ∈ quasithinOmegaOneCenter T)
    (hθ : ∀ c ∈ quasithinOmegaOneCenter T, c ∈ Subgroup.centralizer (L : Set G) →
      thetaOf (Subgroup.centralizer ({c * (e : G)} : Set G)) ≤ lTheta L e)
    {c c' g : G} (hcL : c ∈ Subgroup.centralizer (L : Set G))
    (hc'Z : c' ∈ quasithinOmegaOneCenter T) (hc'L : c' ∈ Subgroup.centralizer (L : Set G))
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) (hgz : g * (c * e) * g⁻¹ = c' * e) : g ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  set f := (MulAut.conj g).toMonoidHom with hf
  have hLθz : lTheta L (e : G) ≤ Subgroup.centralizer ({c * (e : G)} : Set G) :=
    (lTheta_mul_eq hcL (e : G)) ▸ lTheta_le_centralizer L (c * e)
  have h1 : (lTheta L (e : G)).map f ≤ lTheta L e := by
    calc (lTheta L (e : G)).map f ≤ (thetaOf (lTheta L (e : G))).map f :=
          Subgroup.map_mono (lTheta_le_thetaOf h hTL hc he heZ)
      _ ≤ thetaOf ((lTheta L (e : G)).map f) := map_thetaOf_le _ f (MulAut.conj g).injective
      _ ≤ thetaOf (Subgroup.centralizer ({c' * (e : G)} : Set G)) := by
          apply A7.theta_mono
          rw [← hgz]
          exact (Subgroup.map_mono hLθz).trans (map_conj_centralizer_le g _)
      _ ≤ lTheta L e := hθ c' hc'Z hc'L
  have heq : (lTheta L (e : G)).map f = lTheta L e :=
    Subgroup.eq_of_le_of_card_ge h1 (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hgLθ : g ∈ Subgroup.normalizer ((lTheta L (e : G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact heq
  have hgN : g ∈ Subgroup.normalizer ((lTheta L (e : G) ⊔ T : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hgLθ, Subgroup.mem_normalizer_iff_map_conj_eq.1 hgT]
  have hgR : g ∈ Subgroup.normalizer ((pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) := by
    rw [← pCoreOf_lTheta_sup h7 h hML hTL hc he heZ]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hgN
  exact normalizer_le_M h5 h hML (pCoreOf_ne_bot_of_vec_six h he)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) hgR

omit [Finite G] in
theorem exists_of_mem_sup_zpowers {e : G} (heZ : e ∈ quasithinOmegaOneCenter T) (he1 : e ≠ 1)
    {x : G} (hx : x ∈ (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) ⊔
      Subgroup.zpowers e) :
    ∃ c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G), x = c ∨ x = c * e := by
  have he2 : orderOf e = 2 := orderOf_eq_prime (sq_eq_one_of_mem_omegaOneCenter T heZ) he1
  have hzZ : Subgroup.zpowers e ≤ quasithinOmegaOneCenter T := Subgroup.zpowers_le.2 heZ
  obtain ⟨c, hc, u, hu, rfl⟩ := exists_mul_of_mem_sup_comm
    (A := quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G))
    (B := Subgroup.zpowers e) (fun a ha b hb => omegaOneCenter_comm T (Subgroup.mem_inf.1 ha).1
      (hzZ hb)) hx
  refine ⟨c, hc, ?_⟩
  rcases A7.mem_zpowers_of_orderOf_two he2 hu with rfl | rfl
  · left
    rw [mul_one]
  · right
    rfl

theorem mem_M_of_conj (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h14 : Stmt3_3_14)
    (h : Hyp331 G T M L D) (hc : Coord322 T L ψ) {e : ↥⁅vPlus L T, L⁆}
    (he : vec ψ e = A7.vecSix) (heZ : (e : G) ∈ quasithinOmegaOneCenter T)
    (hθ : ∀ c ∈ quasithinOmegaOneCenter T, c ∈ Subgroup.centralizer (L : Set G) →
      thetaOf (Subgroup.centralizer ({c * (e : G)} : Set G)) ≤ lTheta L e)
    {z g : G} (hz : z ∈ (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) ⊔
      Subgroup.zpowers (e : G)) (hz1 : z ≠ 1)
    (hgz : g * z * g⁻¹ ∈ (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) ⊔
      Subgroup.zpowers (e : G)) (hgT : g ∈ Subgroup.normalizer (T : Set G)) : g ∈ M := by
  have he1 := coe_ne_one_of_vec_six he
  obtain ⟨hML, -⟩ := h14 G T M L D h
  obtain ⟨c, hcC, hz'⟩ := exists_of_mem_sup_zpowers heZ he1 hz
  obtain ⟨c', hc'C, hgz'⟩ := exists_of_mem_sup_zpowers heZ he1 hgz
  rcases hz' with rfl | rfl <;> rcases hgz' with hgz' | hgz'
  · exact mem_M_of_conj_mem_centralizer h5 h hML hcC.1 hcC.2 hz1 (hgz' ▸ hc'C.1)
      (hgz' ▸ hc'C.2)
  · exact (false_of_conj_eq_mul h hc he hθ hcC.2 hc'C.1 hc'C.2 hgz').elim
  · refine (false_of_conj_eq_mul h hc he hθ (g := g⁻¹) (z := g * (c * e) * g⁻¹)
      (hgz' ▸ hc'C.2) hcC.1 hcC.2 ?_).elim
    group
  · exact mem_M_of_conj_eq_mul h5 h7 h14 h hc he heZ hθ hcC.2 hc'C.1 hc'C.2 hgT hgz'

end Theta

section Center

variable {ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)}

theorem vecTF_eq : vecTF = vecZO + A7.vecSix := by
  decide +kernel

theorem exists_eq_of_mem_omegaOneCenter (h : Hyp331 G T M L D) (hML : mPlus L T = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hc : Coord322 T L ψ) {a b : ↥⁅vPlus L T, L⁆}
    (ha : vec ψ a = vecZO) (hb : vec ψ b = A7.vecSix) {x : G}
    (hx : x ∈ quasithinOmegaOneCenter T) :
    ∃ c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G),
      x = c ∨ x = b * c ∨ x = a * c ∨ x = a * b * c := by
  have hdec := h.vPlus_decomp.2
  rw [hML] at hdec
  have hVe := (Hyp331.vPlus_reduced h.toSetup331).2.1
  have hVc : ∀ u ∈ vPlus L T, ∀ v ∈ vPlus L T, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hWV := L3317.commV_le_vPlus h
  have hZV : quasithinOmegaOneCenter T ≤ vPlus L T := le_conjClosure _ _
  have hxV : x ∈ ⁅vPlus L T, L⁆ ⊔
      quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := hdec ▸ hZV hx
  obtain ⟨w, hw, c, hcC, rfl⟩ := exists_mul_of_mem_sup_comm (A := ⁅vPlus L T, L⁆)
    (B := quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G))
    (fun u hu v hv => hVc u (hWV hu) v (hZV (Subgroup.mem_inf.1 hv).1)) hxV
  have hwZ : w ∈ quasithinOmegaOneCenter T := by
    have hw' : w = (w * c) * c⁻¹ := by group
    rw [hw']
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hcC.1)
  refine ⟨c, hcC, ?_⟩
  rcases (mem_Z_iff h hTL hc ⟨w, hw⟩).1 hwZ with h0 | h1 | h2 | h3
  · left
    have h' : (⟨w, hw⟩ : ↥⁅vPlus L T, L⁆) = 1 := (A7.vec_eq_zero_iff ψ _).1 h0
    rw [show w = 1 from congrArg Subtype.val h', one_mul]
  · right; right; left
    have h' : (⟨w, hw⟩ : ↥⁅vPlus L T, L⁆) = a := A7.vec_injective ψ (h1.trans ha.symm)
    rw [show w = (a : G) from congrArg Subtype.val h']
  · right; right; right
    have h' : (⟨w, hw⟩ : ↥⁅vPlus L T, L⁆) = a * b :=
      A7.vec_injective ψ (by rw [h2, A7.vec_mul, ha, hb, vecTF_eq])
    rw [show w = (a : G) * b from congrArg Subtype.val h']
  · right; left
    have h' : (⟨w, hw⟩ : ↥⁅vPlus L T, L⁆) = b := A7.vec_injective ψ (h3.trans hb.symm)
    rw [show w = (b : G) from congrArg Subtype.val h']

theorem omegaOneCenter_inf_centralizer_eq_bot (h5 : Stmt3_3_5) (h7 : Stmt3_3_7)
    (h14 : Stmt3_3_14) (h : Hyp331 G T M L D) (hc : Coord322 T L ψ)
    {a b : ↥⁅vPlus L T, L⁆} (ha : vec ψ a = vecZO) (hb : vec ψ b = A7.vecSix)
    (hθ : ∀ c ∈ quasithinOmegaOneCenter T, c ∈ Subgroup.centralizer (L : Set G) →
      thetaOf (Subgroup.centralizer ({c * (b : G)} : Set G)) ≤ lTheta L b) :
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  set Z := quasithinOmegaOneCenter T with hZ
  set C := Z ⊓ Subgroup.centralizer (L : Set G) with hC
  set Zθ := C ⊔ Subgroup.zpowers (b : G) with hZθ
  have haZ : (a : G) ∈ Z := (mem_Z_iff h hTL hc a).2 (Or.inr (Or.inl ha))
  have hbZ : (b : G) ∈ Z := (mem_Z_iff h hTL hc b).2 (Or.inr (Or.inr (Or.inr hb)))
  have ha2 : (a : G) * a = 1 := by rw [← sq]; exact sq_eq_one_of_mem_omegaOneCenter T haZ
  have hb1 := coe_ne_one_of_vec_six hb
  obtain ⟨d, hdD, hdM⟩ := exists_mem_D_not_mem_M h
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hdZ : ∀ x ∈ Z, d * x * d⁻¹ ∈ Z := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_quasithinOmegaOneCenter T hdT) x).1 hx
  have hcos : ∀ x ∈ Z, x ∈ Zθ ∨ (a : G)⁻¹ * x ∈ Zθ := by
    intro x hx
    obtain ⟨c, hcC, hx'⟩ := exists_eq_of_mem_omegaOneCenter h hML hTL hc ha hb hx
    have hc' : c ∈ Zθ := Subgroup.mem_sup_left hcC
    have hbc : (b : G) * c ∈ Zθ :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) hc'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact Or.inl hc'
    · exact Or.inl hbc
    · right
      rw [← mul_assoc, inv_mul_cancel, one_mul]
      exact hc'
    · right
      rw [show (a : G)⁻¹ * (a * b * c) = b * c by group]
      exact hbc
  have hout : ∀ x ∈ Zθ, x ≠ 1 → (a : G)⁻¹ * (d * x * d⁻¹) ∈ Zθ := by
    intro x hx hx1
    have hxZ : x ∈ Z := sup_le inf_le_left (Subgroup.zpowers_le.2 hbZ) hx
    rcases hcos _ (hdZ x hxZ) with h1 | h1
    · exact absurd (mem_M_of_conj h5 h7 h14 h hc hb (hbZ) hθ hx hx1 h1 hdT) hdM
    · exact h1
  rw [eq_bot_iff]
  intro c hcC
  rw [Subgroup.mem_bot]
  by_contra hc1
  have hcb1 : c * (b : G) ≠ 1 := by
    intro h1
    have hbc : (b : G) = c⁻¹ := eq_inv_of_mul_eq_one_right h1
    refine hb1 (congrArg Subtype.val (eq_one_of_centralizer hc b fun l hl => ?_))
    rw [hbc]
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ hcC.2) l hl
  have h1 := hout c (Subgroup.mem_sup_left hcC) hc1
  have h2 := hout b (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) hb1
  set u := (a : G)⁻¹ * (d * c * d⁻¹) with hu
  set v := (a : G)⁻¹ * (d * b * d⁻¹) with hv
  have huZ : u ∈ Z := sup_le inf_le_left (Subgroup.zpowers_le.2 hbZ) h1
  have hprod : d * (c * b) * d⁻¹ = u * v := by
    have hau : (a : G) * u = u * a := omegaOneCenter_comm T haZ huZ
    calc d * (c * b) * d⁻¹ = (a * u) * (a * v) := by rw [hu, hv]; group
      _ = (u * a) * (a * v) := by rw [hau]
      _ = u * (a * a) * v := by group
      _ = u * v := by rw [ha2, mul_one]
  have h4 : d * (c * b) * d⁻¹ ∈ Zθ := hprod ▸ Subgroup.mul_mem _ h1 h2
  exact hdM (mem_M_of_conj h5 h7 h14 h hc hb hbZ hθ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left hcC) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) hcb1 h4 hdT)

theorem exists_conj_eq (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h14 : Stmt3_3_14)
    (h : Hyp331 G T M L D) (hc : Coord322 T L ψ) {a b : ↥⁅vPlus L T, L⁆}
    (ha : vec ψ a = vecZO) (hb : vec ψ b = A7.vecSix)
    (hθ : ∀ c ∈ quasithinOmegaOneCenter T, c ∈ Subgroup.centralizer (L : Set G) →
      thetaOf (Subgroup.centralizer ({c * (b : G)} : Set G)) ≤ lTheta L b) :
    ∃ d ∈ D, d * (a : G) * d⁻¹ = b := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hC := omegaOneCenter_inf_centralizer_eq_bot h5 h7 h14 h hc ha hb hθ
  set Z := quasithinOmegaOneCenter T with hZ
  have haZ : (a : G) ∈ Z := (mem_Z_iff h hTL hc a).2 (Or.inr (Or.inl ha))
  have hbZ : (b : G) ∈ Z := (mem_Z_iff h hTL hc b).2 (Or.inr (Or.inr (Or.inr hb)))
  have ha2 : (a : G) * a = 1 := by rw [← sq]; exact sq_eq_one_of_mem_omegaOneCenter T haZ
  have hb1 := coe_ne_one_of_vec_six hb
  have ha1 : (a : G) ≠ 1 := by
    intro h1
    have h2 : a = 1 := Subtype.ext h1
    rw [h2, A7.vec_one] at ha
    exact absurd ha (by decide +kernel)
  have hZ4 : ∀ x ∈ Z, x = 1 ∨ x = b ∨ x = a ∨ x = a * b := by
    intro x hx
    obtain ⟨c, hcC, hx'⟩ := exists_eq_of_mem_omegaOneCenter h hML hTL hc ha hb hx
    rw [hC, Subgroup.mem_bot] at hcC
    subst hcC
    simpa using hx'
  obtain ⟨d, hdD, hdM⟩ := exists_mem_D_not_mem_M h
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hdZ : ∀ x ∈ Z, d * x * d⁻¹ ∈ Z := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_quasithinOmegaOneCenter T hdT) x).1 hx
  have hbθ : (b : G) ∈ (Z ⊓ Subgroup.centralizer (L : Set G)) ⊔ Subgroup.zpowers (b : G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hdb : d * b * d⁻¹ ≠ b := by
    intro h1
    apply hdM
    refine mem_M_of_conj h5 h7 h14 h hc hb hbZ hθ hbθ hb1 ?_ hdT
    rw [h1]
    exact hbθ
  have hne : ∀ x : G, x ≠ 1 → d * x * d⁻¹ ≠ 1 := fun x hx h1 => hx (by
    calc x = d⁻¹ * (d * x * d⁻¹) * d := by group
      _ = 1 := by rw [h1]; group)
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf (⟨d, hdD⟩ : D) ∣ Nat.card D := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact h.Dodd.of_dvd_nat h1
  rcases hZ4 _ (hdZ _ hbZ) with h1 | h1 | h1 | h1
  · exact absurd h1 (hne _ hb1)
  · exact absurd h1 hdb
  ·
    refine ⟨d⁻¹, inv_mem hdD, ?_⟩
    rw [← h1]
    group
  · rcases hZ4 _ (hdZ _ haZ) with h2 | h2 | h2 | h2
    · exact absurd h2 (hne _ ha1)
    · exact ⟨d, hdD, h2⟩
    ·
      exfalso
      have hsq : d ^ 2 * b * (d ^ 2)⁻¹ = b := by
        calc d ^ 2 * b * (d ^ 2)⁻¹ = d * (d * b * d⁻¹) * d⁻¹ := by rw [sq]; group
          _ = d * (a * b) * d⁻¹ := by rw [h1]
          _ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
          _ = a * (a * b) := by rw [h2, h1]
          _ = b := by rw [← mul_assoc, ha2, one_mul]
      have hcomm : Commute (d ^ 2) b := by
        show d ^ 2 * b = b * d ^ 2
        calc d ^ 2 * b = d ^ 2 * b * (d ^ 2)⁻¹ * d ^ 2 := by group
          _ = b * d ^ 2 := by rw [hsq]
      have h3 : d * b = b * d := (commute_of_sq hodd hcomm).eq
      apply hdb
      rw [h3, mul_inv_cancel_right]
    ·
      exfalso
      have h3 : d * a * d⁻¹ = d * b * d⁻¹ := by rw [h1, h2]
      have hab : a = b := Subtype.ext (mul_left_cancel (mul_right_cancel h3))
      rw [hab, hb] at ha
      exact absurd ha (by decide +kernel)

end Center

end CFSG.Quasithin.H13.L3322
