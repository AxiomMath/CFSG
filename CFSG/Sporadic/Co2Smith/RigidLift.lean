module

public import CFSG.Sporadic.Co2Smith.RigidForm
public import CFSG.Sporadic.Co2Smith.RigidPin

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Certificates.ExtraspecialNF

universe u

@[expose] noncomputable def yw
    (e0 e1 e2 : Bool) : S0 :=
  (if e0 then frS 0 else 1) * (if e1 then frS 2 else 1) * (if e2 then frS 4 else 1)

theorem frS0_comm_ite
    (k : ℕ) (hk : k = 2 ∨ k = 4) (e : Bool) :
    frS 0 * (if e then frS k else 1) = (if e then frS k else 1) * frS 0 := by
  cases e
  · simp
  · rcases hk with rfl | rfl
    · exact frS_comm' (k := 0) (l := 2) (by norm_num) (by norm_num) (by norm_num)
    · exact frS_comm' (k := 0) (l := 4) (by norm_num) (by norm_num) (by norm_num)

namespace LocalConfig

variable (c : LocalConfig.{u})

theorem Bm_eq_zero_of
    (h : ∀ m m' : c.M, c.Bm m m' = 0) : False := by
  obtain ⟨x, hx, y, hy, hxy⟩ := c.loc.pCore_noncomm
  have h1 := h (c.piM ⟨x, hx⟩) (c.piM ⟨y, hy⟩)
  rw [c.Bm_piM] at h1
  have h2 := c.comm_eq ⟨x, hx⟩ ⟨y, hy⟩
  rw [h1, ZMod.val_zero, pow_zero, mul_one] at h2
  exact hxy (congrArg Subtype.val h2)

theorem Bm_β_left
    (u : Fin 8 → ZMod 2) (m : c.M) :
    c.Bm (c.β u) m = ∑ a, u a * c.Bm (c.v a) m := by
  rw [β]
  induction (Finset.univ : Finset (Fin 8)) using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    have := c.Bm_mul_left 1 1 m
    rw [one_mul] at this
    exact add_eq_self this.symm
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, c.Bm_mul_left, ih]
    congr 1
    rcases zmod_two_cases (u a) with h | h <;> rw [h]
    · rw [ZMod.val_zero, pow_zero, zero_mul]
      have := c.Bm_mul_left 1 1 m
      rw [one_mul] at this
      exact add_eq_self this.symm
    · rw [val_one_two, pow_one, one_mul]

theorem β0_eq_one :
    c.β0 = 1 := by
  rcases zmod_two_cases c.β0 with h | h
  · exfalso
    apply c.Bm_eq_zero_of
    intro m m'
    obtain ⟨u, rfl⟩ := c.β_surjective m
    obtain ⟨u', rfl⟩ := c.β_surjective m'
    rw [c.Bm_β_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [c.Bm_symm, c.Bm_β_left]
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← vcode_bits a, ← vcode_bits b, c.v_vcode, c.v_vcode, c.Bm_vv, h]
    split_ifs <;> simp
  · exact h

theorem Bm_v
    (a b : Fin 8) : c.Bm (c.v a) (c.v b) = J7 a b := by
  have key : ∀ a b : Fin 8, ((a.val.testBit 0 ≠ b.val.testBit 0 ∧
      a.val.testBit 1 ≠ b.val.testBit 1 ∧ a.val.testBit 2 ≠ b.val.testBit 2) ↔
      a.val + b.val = 7) := by decide
  have h := c.Bm_vv (a.val.testBit 0) (a.val.testBit 1) (a.val.testBit 2) (b.val.testBit 0)
    (b.val.testBit 1) (b.val.testBit 2)
  rw [← c.v_vcode, ← c.v_vcode, vcode_bits, vcode_bits, c.β0_eq_one] at h
  rw [h, J7]
  exact if_congr (key a b) rfl rfl

noncomputable abbrev cy (e : c.E) : c.E := c.cE (c.fr 0) e

theorem cE_center
    (h : c.H) {e : c.E} (he : e ∈ Subgroup.center c.E) : c.cE h e = e := by
  rcases (c.mem_center_iff e).mp he with rfl | rfl
  · exact map_one _
  · exact c.cE_zE h

theorem sq_mem_center
    (e : c.E) : e * e ∈ Subgroup.center c.E := by
  rw [← c.piM_eq_one_iff, map_mul]
  exact c.sq_M _

theorem eq_mul_center
    {e e' : c.E} (h : c.piM e = c.piM e') :
    ∃ k ∈ Subgroup.center c.E, e' = e * k :=
  ⟨e⁻¹ * e', QuotientGroup.eq.mp h, by group⟩

@[expose] noncomputable def normY (e : c.E) : c.E := e * c.cy e * c.cy (c.cy e)

theorem w_Y1 :

    c.mA (frS 0) (c.mA (frS 0) c.w) = c.w * c.mA (frS 0) c.w := c.yy0 _

theorem piM_cy
    (e : c.E) : c.piM (c.cy e) = c.mA (frS 0) (c.piM e) := (c.mA_piM_fr 0 e).symm

theorem normY_center
    {e : c.E} (he : c.piM e = c.w) : c.normY e ∈ Subgroup.center c.E := by
  rw [← c.piM_eq_one_iff, normY, map_mul, map_mul, c.piM_cy, c.piM_cy, c.piM_cy, he, c.w_Y1]
  exact c.sq_M _

theorem zE_commute
    (x : c.E) : Commute c.zE x := (c.zE_comm x).symm

theorem normY_mul_z
    (e : c.E) : c.normY (e * c.zE) = c.normY e * c.zE := by
  simp only [normY, cy, map_mul, c.cE_zE]
  set a := c.cE (c.fr 0) e
  set b := c.cE (c.fr 0) a
  have hzz : Commute (c.zE * c.zE) b :=
    (c.zE_commute b).mul_left (c.zE_commute b)
  calc e * c.zE * (a * c.zE) * (b * c.zE)
      = e * a * (c.zE * c.zE) * (b * c.zE) := by rw [(c.zE_commute a).mul_mul_mul_comm]
    _ = e * a * b * (c.zE * c.zE * c.zE) := by rw [hzz.mul_mul_mul_comm]
    _ = e * a * b * c.zE := by rw [c.zE_sq, one_mul]

theorem lift_w_sq
    {e : c.E} (he : c.piM e = c.w) : e * e = 1 := by
  set e' := c.cy e
  set e'' := c.cy e'
  have hss := c.sq_mem_center e
  have h1 : c.piM e'' = c.piM (e * e') := by
    rw [show e'' = c.cy (c.cy e) from rfl, show e' = c.cy e from rfl, map_mul, c.piM_cy,
      c.piM_cy, he, c.w_Y1]
  obtain ⟨k, hk, hk0⟩ := c.eq_mul_center h1
  have hkk : k * k = 1 := by
    rcases (c.mem_center_iff k).mp hk with rfl | rfl
    · rw [one_mul]
    · exact c.zE_sq
  have hk' : e'' = e * e' * k := by rw [hk0, mul_assoc, hkk, mul_one]
  have hcomm : ∀ x : c.E, Commute k x := fun x => (Subgroup.mem_center_iff.mp hk x).symm
  have he'2 : e' * e' = e * e := by
    rw [← map_mul]
    exact c.cE_center _ hss
  have he''2 : e'' * e'' = e * e := by
    rw [← map_mul, he'2]
    exact c.cE_center _ hss
  have hc : c.cf e' e = 0 := by
    rw [← c.Bm_piM]
    have h0 : c.piM e = c.v 0 := he
    have h1' : c.piM e' = c.v 1 := by
      rw [show e' = c.cy e from rfl, c.piM_cy, he]
      rfl
    rw [h0, h1', c.Bm_v]
    rfl
  have hc' := c.comm_eq e' e
  rw [hc, ZMod.val_zero, pow_zero, mul_one] at hc'
  have key : e * e = e * e * (e * e) := by
    calc e * e = e'' * e'' := he''2.symm
      _ = e * e' * k * (e * e' * k) := by rw [hk']
      _ = e * e' * (e * e') * (k * k) := by rw [(hcomm (e * e')).mul_mul_mul_comm]
      _ = e * (e' * e) * e' := by rw [hkk, mul_one]; simp only [mul_assoc]
      _ = e * e * (e' * e') := by rw [hc']; simp only [mul_assoc]
      _ = e * e * (e * e) := by rw [he'2]
  have := mul_left_cancel (a := e * e) (key.symm.trans (mul_one (e * e)).symm)
  exact this

open scoped Classical in
@[expose] noncomputable def wh :
    c.E :=
  if c.normY (c.lift c.w) = 1 then c.lift c.w else c.lift c.w * c.zE

theorem piM_wh :
    c.piM c.wh = c.w := by
  rw [wh]
  split_ifs
  · exact c.piM_lift c.w
  · rw [map_mul, c.piM_lift, (c.piM_eq_one_iff _).mpr c.zE_mem_center, mul_one]

theorem wh_sq :
    c.wh * c.wh = 1 := c.lift_w_sq c.piM_wh

theorem norm_wh :
    c.normY c.wh = 1 := by
  rw [wh]
  split_ifs with h
  · exact h
  · rw [c.normY_mul_z]
    rcases (c.mem_center_iff _).mp (c.normY_center (c.piM_lift c.w)) with h' | h'
    · exact absurd h' h
    · rw [h', c.zE_sq]

@[expose] noncomputable def vhv
    (e0 e1 e2 : Bool) : c.E := c.cE (c.ℓ (yw e0 e1 e2)) c.wh

@[expose] noncomputable def vh
    (a : Fin 8) : c.E :=
  c.vhv (a.val.testBit 0) (a.val.testBit 1) (a.val.testBit 2)

theorem vh_vcode
    (e0 e1 e2 : Bool) : c.vh (vcode e0 e1 e2) = c.vhv e0 e1 e2 := by
  cases e0 <;> cases e1 <;> cases e2 <;> rfl

theorem mA_ite
    (k : ℕ) (e : Bool) (m : c.M) :
    c.mA (if e then frS k else 1) m = c.yb k e m := by
  cases e
  · exact c.mA_one m
  · rfl

theorem piM_vhv
    (e0 e1 e2 : Bool) : c.piM (c.vhv e0 e1 e2) = c.vv e0 e1 e2 := by
  rw [vhv, ← c.mA_piM, c.piM_wh, yw, c.mA_mul, c.mA_mul, c.mA_ite, c.mA_ite, c.mA_ite]
  rfl

theorem piM_vh
    (a : Fin 8) : c.piM (c.vh a) = c.v a := c.piM_vhv _ _ _

theorem vh_sq
    (a : Fin 8) : c.vh a * c.vh a = 1 := by
  rw [vh, vhv, ← map_mul, c.wh_sq, map_one]

theorem cf_vh
    (a b : Fin 8) : c.cf (c.vh a) (c.vh b) = J7 a b := by
  rw [← c.Bm_piM, c.piM_vh, c.piM_vh, c.Bm_v]

theorem rel_vh :
    Rel c.zE c.vh J7 where
  z_sq := c.zE_sq
  z_comm i := (c.zE_comm (c.vh i)).symm
  q_sq := c.vh_sq
  comm i j := by rw [c.comm_eq, c.cf_vh]

theorem piM_mon
    (u : Fin 8 → ZMod 2) : c.piM (mon c.vh u) = c.β u := by
  rw [mon, map_list_prod, List.map_ofFn, β, ← List.prod_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, map_pow, c.piM_vh]

theorem piM_nf
    (s : ZMod 2) (u : Fin 8 → ZMod 2) : c.piM (nf c.zE c.vh s u) = c.β u := by
  rw [nf, map_mul, map_pow, (c.piM_eq_one_iff _).mpr c.zE_mem_center, one_pow, one_mul,
    c.piM_mon]

theorem eq_nf_of_piM
    {e : c.E} {u : Fin 8 → ZMod 2} (h : c.piM e = c.β u) :
    ∃ σ : ZMod 2, e = nf c.zE c.vh σ u := by
  obtain ⟨k, hk, rfl⟩ := c.eq_mul_center ((c.piM_nf 0 u).trans h.symm)
  rcases (c.mem_center_iff k).mp hk with rfl | rfl
  · exact ⟨0, mul_one _⟩
  · refine ⟨1, ?_⟩
    have h := nf_mul_zpow c.rel_vh 0 1 u
    rw [val_one_two, pow_one, zero_add] at h
    exact h

theorem nf_bijective :
    Function.Bijective (Function.uncurry (nf c.zE c.vh)) := by
  have hsurj : Function.Surjective (Function.uncurry (nf c.zE c.vh)) := by
    intro e
    obtain ⟨u, hu⟩ := c.β_surjective (c.piM e)
    obtain ⟨σ, hσ⟩ := c.eq_nf_of_piM hu.symm
    exact ⟨(σ, u), hσ.symm⟩
  refine hsurj.bijective_of_nat_card_le ?_
  rw [c.card_E, Nat.card_prod, Nat.card_zmod, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem frame_vh
    (k : ℕ) (hk : k < 9) (a : Fin 8) :
    ∃ σ : ZMod 2, c.cE (c.fr k) (c.vh a) = nf c.zE c.vh σ fun b => frameMat k b a := by
  apply c.eq_nf_of_piM
  rw [fr, ← c.mA_piM, c.piM_vh, ← c.β_single, c.rep_frame k hk, Matrix.mulVec_single_one]
  rfl

end LocalConfig

end CFSG.Sporadic.Co2Smith
