module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6Ctx
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma6

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem Z_le_CT (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
  ((Subgroup.closure_le _).mpr fun _ hz => hz.1).trans inf_le_right

omit [Finite G] in
theorem Z_le_T (T : Subgroup G) : quasithinOmegaOneCenter T ≤ T :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1.1

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem facts4 : z ∈ E ∧ E = Subgroup.zpowers v ⊔ Subgroup.zpowers z ∧
    ∀ t ∈ T, t * v * t⁻¹ = v ∨ t * v * t⁻¹ = v * z :=
  cx_four_subgroup c.cx c.f c.card16 c.nat c.EV c.E4 c.TE c.vE c.vL

theorem R1_facts : c.R1 = T ⊓ Subgroup.centralizer ({v} : Set G) ∧ c.R1.relIndex T = 2 :=
  cx_relIndex_eq_two c.cx c.f c.card16 c.nat c.EV c.E4 c.TE c.vE c.vL

theorem R1_le_NV : c.R1 ≤ Subgroup.normalizer (V : Set G) := c.R1_le_T.trans c.f.T_le

theorem card_autOn_T : Nat.card (autOn T V) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [c.Tbar]
  obtain ⟨hle, hp, hodd⟩ := c.Tsyl
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have h1 := ((autOn (T ⊓ L) V).subgroupOf (autOn L V)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hk, c.card168] at h1
  have hk3 : k = 3 := by
    have h2 : 2 ^ k ∣ 2 ^ 3 * 21 := Dvd.intro _ (by rw [h1]; norm_num)
    have h3 : 2 ^ 3 ∣ 2 ^ k * ((autOn (T ⊓ L) V).subgroupOf (autOn L V)).index :=
      Dvd.intro 21 (by rw [h1]; norm_num)
    have hc1 : Nat.Coprime (2 ^ k) 21 := Nat.Coprime.pow_left k (by norm_num)
    have hc2 : Nat.Coprime (2 ^ 3) ((autOn (T ⊓ L) V).subgroupOf (autOn L V)).index :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    exact le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1
      (hc1.dvd_of_dvd_mul_right h2)) ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1
      (hc2.dvd_of_dvd_mul_right h3))
  rw [hk, hk3]
  norm_num

theorem R1_not_le_CV : ¬ c.R1 ≤ Subgroup.centralizer (V : Set G) := by
  intro h
  have hRQ : c.R1 ≤ T ⊓ Subgroup.centralizer (V : Set G) := le_inf c.R1_le_T h
  have h8 := c.card_autOn_T
  rw [card_autOn_eq_relIndex c.f.T_le] at h8
  have h2 := c.R1_facts.2
  have hdvd : (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T ∣ c.R1.relIndex T :=
    Subgroup.relIndex_dvd_of_le_left T hRQ
  rw [h8, h2] at hdvd
  norm_num at hdvd

theorem inf_centralizer_R1 : V ⊓ Subgroup.centralizer (c.R1 : Set G) = E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := c.cx.hyp
  obtain ⟨D⟩ := c.nat.toL3Coord
  have h16 : Nat.card ↥V = 16 := by rw [c.card16]; norm_num
  have hcommGr := commV_autOn_eq_top c.f.normalizes c.f.commutator
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcommGr h16
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using c.f.sq w w.2)
  obtain ⟨-, -, -, h4⟩ := B4_8_2 hW h16 c.nat hind
  have hER : E ≤ V ⊓ Subgroup.centralizer (c.R1 : Set G) :=
    le_inf c.EV (Subgroup.le_centralizer_iff.mp inf_le_right)
  refine (Subgroup.eq_of_le_of_card_ge hER ?_).symm
  rw [c.E4]
  obtain ⟨r, hrR, hrV⟩ : ∃ r ∈ c.R1, r ∉ Subgroup.centralizer (V : Set G) := by
    by_contra h
    push Not at h
    exact c.R1_not_le_CV h
  have hrN : r ∈ Subgroup.normalizer (V : Set G) := c.R1_le_NV hrR
  have ha : conjAct V ⟨r, hrN⟩ ∈ autOn c.R1 V :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hrR)
  have ha1 : conjAct V ⟨r, hrN⟩ ≠ 1 := fun h => hrV (A4.conjAct_eq_one_iff.1 h)
  have hRp : IsPGroup 2 (autOn c.R1 V) := isPGroup_autOn (hyp.sylow.1.to_le c.R1_le_T)
  have hne : Nat.card (autOn c.R1 V) ≠ 1 := by
    intro h1
    have hbot := Subgroup.eq_bot_of_card_eq _ h1
    apply ha1
    have hmem := ha
    rw [hbot] at hmem
    exact hmem
  have h2dvd : 2 ∣ Nat.card (autOn c.R1 V) := by
    obtain ⟨k, hk⟩ := hRp.exists_card_eq
    rw [hk] at hne ⊢
    rcases k with _ | k
    · simp at hne
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(autOn c.R1 V)) 2 h2dvd
  have hbL : (b : MulAut ↥V) ∈ autOn L V := by
    have h1 : (b : MulAut ↥V) ∈ autOn T V := A4.autOn_mono c.R1_le_T b.2
    rw [c.Tbar] at h1
    exact c.Tsyl.1 h1
  have hb1 : (b : MulAut ↥V) ≠ 1 := by
    intro h
    have : b = 1 := Subtype.ext h
    rw [this, orderOf_one] at hb
    norm_num at hb
  have hb2 : (b : MulAut ↥V) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hb, pow_orderOf_eq_one, Subgroup.coe_one]
  obtain ⟨-, hrk⟩ := h4 _ hbL hb1 hb2
  have hfixb : Nat.card (fixV (Subgroup.zpowers (b : MulAut ↥V))) = 4 := by
    rw [card_eq_two_pow hW, hrk]
    norm_num
  rw [← hfixb, ← card_subgroupOf_eq_card_inf, ← fixV_autOn_eq c.R1_le_NV]
  exact Subgroup.card_le_of_le fun v hv x hx => hv x ((Subgroup.zpowers_le.2 b.2) hx)

theorem Z_le_CL : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (L : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp c.ZL

theorem z_mem_Z : z ∈ quasithinOmegaOneCenter T := by
  have hzV : z ∈ V := c.f.mem_zV.1
  refine Subgroup.subset_closure ⟨⟨c.f.le_T hzV, ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_iff.2 fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.1 (c.f.T_le_centralizer c.cx.hyp.normalizes ht)
  · rw [← c.f.order]
    exact pow_orderOf_eq_one z

theorem Z_inf_V : quasithinOmegaOneCenter T ⊓ V = Subgroup.zpowers z := by
  refine le_antisymm (fun x hx => ?_) (le_inf (Subgroup.zpowers_le.2 c.z_mem_Z)
    (Subgroup.zpowers_le.2 c.f.mem_zV.1))
  rw [← c.f.zV]
  exact ⟨hx.2, cx_inf_centralizer_T_le c.cx c.f c.card16 c.nat ⟨hx.2, N1246.Z_le_CT T hx.1⟩⟩

theorem omega_R1_le_Q : omegaOneCenterOf c.R1 ≤ pCoreOf 2 (L ⊔ T) := by
  intro x hx
  have hxc := A4.omegaOneCenterOf_le_centerOf c.R1 hx
  have hxR : x ∈ c.R1 := A4.centerOf_le c.R1 hxc
  have hxC : x ∈ Subgroup.centralizer (c.R1 : Set G) := A4.centerOf_le_centralizer c.R1 hxc
  exact c.char ⟨(le_sup_right : T ≤ L ⊔ T) (c.R1_le_T hxR),
    Subgroup.centralizer_le c.Q_le_R1 hxC⟩

theorem omega_R1_le : omegaOneCenterOf c.R1 ≤ quasithinOmegaOneCenter T ⊔ E := by
  have hZN : quasithinOmegaOneCenter T ≤ Subgroup.normalizer (V : Set G) :=
    (N1246.Z_le_T T).trans c.f.T_le
  rw [omegaOneCenterOf, omegaOneOf, Subgroup.closure_le]
  rintro x ⟨hxc, hx2⟩
  have hxR : x ∈ c.R1 := A4.centerOf_le c.R1 hxc
  have hxC : x ∈ Subgroup.centralizer (c.R1 : Set G) := A4.centerOf_le_centralizer c.R1 hxc
  have hxQ : x ∈ pCoreOf 2 (L ⊔ T) := c.omega_R1_le_Q (Subgroup.subset_closure ⟨hxc, hx2⟩)
  have hxW : x ∈ omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) := by
    refine Subgroup.subset_closure ⟨⟨hxQ, ?_⟩, hx2⟩
    exact Subgroup.centralizer_le c.Q_le_R1 hxC
  rw [c.ZQ] at hxW
  have hxmem : x ∈ (quasithinOmegaOneCenter T : Set G) * (V : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZN]
    exact hxW
  obtain ⟨a, ha, w, hw, rfl⟩ := hxmem
  have haC : a ∈ Subgroup.centralizer (c.R1 : Set G) :=
    Subgroup.centralizer_le (inf_le_left : (c.R1 : Set G) ⊆ T) ((N1246.Z_le_CT T ha))
  have hwC : w ∈ Subgroup.centralizer (c.R1 : Set G) := by
    have := (Subgroup.centralizer (c.R1 : Set G)).mul_mem
      ((Subgroup.centralizer (c.R1 : Set G)).inv_mem haC) hxC
    simpa using this
  have hwE : w ∈ E := c.inf_centralizer_R1 ▸ ⟨hw, hwC⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hwE)

theorem Z_E_comm : ∀ a ∈ quasithinOmegaOneCenter T, ∀ e ∈ E, a * e = e * a := fun _ ha e he =>
  (Subgroup.mem_centralizer_iff.1 ((N1246.Z_le_CT T ha)) e (c.f.le_T (c.EV he))).symm

theorem Z_inf_E : quasithinOmegaOneCenter T ⊓ E = Subgroup.zpowers z := by
  refine le_antisymm ?_ (le_inf (Subgroup.zpowers_le.2 c.z_mem_Z)
    (Subgroup.zpowers_le.2 c.facts4.1))
  rw [← c.Z_inf_V]
  exact inf_le_inf_left _ c.EV

theorem card_sup_ZE : Nat.card ↥(quasithinOmegaOneCenter T ⊔ E) =
    2 * Nat.card (quasithinOmegaOneCenter T) := by
  have h := B2F.card_sup_mul_card_inf_of_commute c.Z_E_comm
  rw [c.Z_inf_E, Nat.card_zpowers, c.f.order, c.E4] at h
  omega

theorem partA (hN : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    quasithinOmegaOneCenter T = Subgroup.zpowers z ∧ omegaOneCenterOf c.R1 = E ∧
      Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (E : Set G) := by
  obtain ⟨g, hgR, hgM⟩ : ∃ g ∈ Subgroup.normalizer (c.R1 : Set G),
      g ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hN h
  set Z := quasithinOmegaOneCenter T with hZdef
  have hZC : Z ⊓ Subgroup.centralizer (L : Set G) = Z := inf_eq_left.2 c.Z_le_CL
  have hdisj := c.disj g hgM
  rw [hZC] at hdisj
  have hZgle : conjSubgroup Z g ≤ quasithinOmegaOneCenter T ⊔ E := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have h1 : g * x * g⁻¹ ∈ omegaOneCenterOf c.R1 := c.Z_le_omega_R1 hx
    have hgi : g⁻¹ ∈ Subgroup.normalizer (omegaOneCenterOf c.R1 : Set G) :=
      A4.normalizer_le_normalizer_omegaOneCenterOf c.R1 (Subgroup.inv_mem _ hgR)
    have h2 := (Subgroup.mem_normalizer_iff.1 hgi (g * x * g⁻¹)).1 h1
    rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h2
    exact c.omega_R1_le h2
  have hZle : Z ≤ quasithinOmegaOneCenter T ⊔ E := le_sup_left
  have hZET : quasithinOmegaOneCenter T ⊔ E ≤ T :=
    sup_le (N1246.Z_le_T T) (c.EV.trans c.f.le_T)
  have hcomm : ∀ a ∈ Z, ∀ b ∈ conjSubgroup Z g, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.1 ((N1246.Z_le_CT T ha)) b (hZET (hZgle hb))).symm
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hdisj, Subgroup.card_bot, mul_one] at hcard
  have hcg : Nat.card (conjSubgroup Z g) = Nat.card Z :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hle : Nat.card ↥(Z ⊔ conjSubgroup Z g) ≤ Nat.card ↥(quasithinOmegaOneCenter T ⊔ E) :=
    Subgroup.card_le_of_le (sup_le hZle hZgle)
  rw [c.card_sup_ZE, hcard, hcg] at hle
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hZ2 : Nat.card Z ≤ 2 := by nlinarith
  have hzZ : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le.2 c.z_mem_Z
  have hZeq : Z = Subgroup.zpowers z := by
    refine (Subgroup.eq_of_le_of_card_ge hzZ ?_).symm
    rw [Nat.card_zpowers, c.f.order]
    exact hZ2
  have hZ1 : omegaOneCenterOf c.R1 = E := by
    refine le_antisymm ?_ ?_
    · have h1 := c.omega_R1_le
      rwa [← hZdef, hZeq, sup_eq_right.2 (Subgroup.zpowers_le.2 c.facts4.1)] at h1
    · rw [omegaOneCenterOf, omegaOneOf]
      intro e he
      refine Subgroup.subset_closure ⟨⟨c.E_le_R1 he, ?_⟩, c.f.sq e (c.EV he)⟩
      exact Subgroup.mem_centralizer_iff.2 fun r hr =>
        (Subgroup.mem_centralizer_iff.1 hr.2 e he).symm
  refine ⟨hZeq, hZ1, fun x hx => ?_⟩
  have h1 := A4.normalizer_le_normalizer_omegaOneCenterOf c.R1 hx
  rwa [hZ1] at h1

end Ctx

end N1246

end CFSG.Quasithin.H13
