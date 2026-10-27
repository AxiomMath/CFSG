module

public import CFSG.Sporadic.FischerOddCore.Fi23Stab
public import CFSG.Sporadic.FischerOddCore.Fi23WitCheck
public import CFSG.Sporadic.Fi23.InvCover
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalFourthDerived

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Free

variable {G : Type*} [Group G] [Finite G]

theorem eq_one_of_mem_oddCore_of_fix {r x : G}
    (hstab : CFSG.oddCore ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {r}) = ⊥)
    {v : ↥(Subgroup.centralizer ({r} : Set G))}
    (hv : v ∈ CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set G)))
    (hvx : (v : G) * x * (v : G)⁻¹ = x) : v = 1 := by
  let C := Subgroup.centralizer ({r} : Set G)
  let V := (CFSG.oddCore C).map C.subtype
  let L := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {r}
  have hWL : V ⊓ Subgroup.centralizer {x} ≤ L := by
    intro w hw
    obtain ⟨⟨c, -, hcw⟩, hwx⟩ := Subgroup.mem_inf.1 hw
    refine Subgroup.mem_inf.2 ⟨hwx, ?_⟩
    rw [← hcw]
    exact c.2
  have hnormal : ((V ⊓ Subgroup.centralizer {x}).subgroupOf L).Normal := by
    refine ⟨fun w hw l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    obtain ⟨⟨c, hc, hcw⟩, hwx⟩ := Subgroup.mem_inf.1 hw
    have hlx := (Subgroup.mem_inf.1 l.2).1
    have hlr := (Subgroup.mem_inf.1 l.2).2
    refine Subgroup.mem_inf.2 ⟨⟨⟨l, hlr⟩ * c * ⟨l, hlr⟩⁻¹,
      (CFSG.oddCore_normal (G := C)).conj_mem c hc _, ?_⟩, ?_⟩
    · rw [map_mul, map_mul, map_inv, hcw]
      rfl
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hlx hwx) (Subgroup.inv_mem _ hlx)
  have hodd : Odd (Nat.card ((V ⊓ Subgroup.centralizer {x}).subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv]
    have hV : Nat.card V = Nat.card (CFSG.oddCore C) :=
      Nat.card_congr ((CFSG.oddCore C).equivMapOfInjective _ C.subtype_injective).toEquiv.symm
    exact Odd.of_dvd_nat (hV ▸ odd_card_oddCore) (Subgroup.card_dvd_of_le inf_le_left)
  have hle := le_oddCore_of_normal hnormal hodd
  rw [hstab, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
  have hbot : V ⊓ Subgroup.centralizer {x} = ⊥ := disjoint_self.1 (hle.mono_right hWL)
  have hmem : (v : G) ∈ V ⊓ Subgroup.centralizer {x} := by
    refine Subgroup.mem_inf.2 ⟨⟨v, hv, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (v : G) * x = (v : G) * x * (v : G)⁻¹ * v := by group
      _ = x * v := by rw [hvx]
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem card_oddCore_dvd {E : Set G} (hE : ∀ g x, x ∈ E → g * x * g⁻¹ ∈ E) {r : G}
    (P : G → Prop) (hPr : ∀ x, P x → x * r = r * x)
    (hstab : ∀ x ∈ E, x * r = r * x →
      CFSG.oddCore ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {r}) = ⊥)
    (hPV : ∀ v ∈ CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set G)), ∀ x, P x →
      P ((v : G) * x * (v : G)⁻¹)) :
    Nat.card (CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set G))) ∣ Nat.card {x : E // P x} := by
  set C := Subgroup.centralizer ({r} : Set G)
  let act : MulAction (CFSG.oddCore C) {x : E // P x} :=
    { smul := fun v x => ⟨⟨((v : C) : G) * x * ((v : C) : G)⁻¹, hE _ _ x.1.2⟩,
        hPV v v.2 x x.2⟩
      one_smul := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        show ((1 : C) : G) * ((x : E) : G) * ((1 : C) : G)⁻¹ = ((x : E) : G)
        simp
      mul_smul := fun v w x => by
        apply Subtype.ext
        apply Subtype.ext
        show (((v : C) * (w : C) : C) : G) * ((x : E) : G) * (((v : C) * (w : C) : C) : G)⁻¹ =
          ((v : C) : G) * (((w : C) : G) * ((x : E) : G) * ((w : C) : G)⁻¹) * ((v : C) : G)⁻¹
        rw [Subgroup.coe_mul]
        group }
  refine card_dvd_of_free (X := {x : E // P x}) fun v x hvx => ?_
  have h : ((v : C) : G) * x * ((v : C) : G)⁻¹ = x :=
    congrArg (fun y : {x : E // P x} => ((y : E) : G)) hvx
  have := eq_one_of_mem_oddCore_of_fix (hstab x x.1.2 (hPr x x.2)) v.2 h
  exact Subtype.ext this

end Free

theorem conj_fix_of_commute {G : Type*} [Group G] {e v x : G} (hev : v * e = e * v)
    (hx : e * x * e⁻¹ = x) : e * (v * x * v⁻¹) * e⁻¹ = v * x * v⁻¹ := by
  calc e * (v * x * v⁻¹) * e⁻¹ = (e * v) * x * (e * v)⁻¹ := by group
    _ = (v * e) * x * (v * e)⁻¹ := by rw [hev]
    _ = v * (e * x * e⁻¹) * v⁻¹ := by group
    _ = v * x * v⁻¹ := by rw [hx]

@[expose] noncomputable def fi23Bray
    (r g : Fi23.J) (e : ℕ) (odd : Bool) : Fi23.J :=
  if odd then g * (r * (g⁻¹ * (r * g))) ^ e else (r * (g⁻¹ * (r * g))) ^ e

theorem rep_fi23BrayT
    {R G Gi : Table} {r g : Fi23.J} (hR : Rep 31671 R r)
    (hG : Rep 31671 G g) (hGi : Rep 31671 Gi g⁻¹) (e : ℕ) (odd : Bool) :
    Rep 31671 (fi23BrayT R G Gi e odd) (fi23Bray r g e odd) := by
  have hBB := Rep.powT (n := 31671) (by norm_num)
    (Rep.compT hR (Rep.compT hGi (Rep.compT hR hG))) e
  cases odd
  · simp only [fi23BrayT, fi23Bray, Bool.false_eq_true, ↓reduceIte]
    exact hBB
  · simp only [fi23BrayT, fi23Bray, ↓reduceIte]
    exact Rep.compT hG hBB

theorem card_fixed3_eq
    {X Y Z : Table} {g h k : Fi23.J} (hX : Rep 31671 X g)
    (hY : Rep 31671 Y h) (hZ : Rep 31671 Z k) :
    Nat.card {x : Fi23.D23 // g * x * g⁻¹ = x ∧ h * x * h⁻¹ = x ∧ k * x * k⁻¹ = x} =
      fi23Common X Y Z := by
  have e1 : {i : Fin 31671 // ap X i.val = i.val ∧ ap Y i.val = i.val ∧ ap Z i.val = i.val} ≃
      {x : Fi23.D23 // g * x * g⁻¹ = x ∧ h * x * h⁻¹ = x ∧ k * x * k⁻¹ = x} :=
    Equiv.subtypeEquiv Fi23.ptD fun i => by
      rw [hX i.val i.isLt, hY i.val i.isLt, hZ i.val i.isLt, Fi23.idx_eq_iff i.isLt i.isLt,
        Fi23.idx_eq_iff i.isLt i.isLt, Fi23.idx_eq_iff i.isLt i.isLt, Fi23.ptD_val]
  have e2 : {i : Fin 31671 // ap X i.val = i.val ∧ ap Y i.val = i.val ∧ ap Z i.val = i.val} ≃
      ((Finset.range 31671).filter fun i => ap X i = i ∧ ap Y i = i ∧ ap Z i = i) :=
    { toFun := fun i => ⟨i.1.1, Finset.mem_filter.2 ⟨Finset.mem_range.2 i.1.2, i.2⟩⟩
      invFun := fun i => ⟨⟨i.1, Finset.mem_range.1 (Finset.mem_filter.1 i.2).1⟩,
        (Finset.mem_filter.1 i.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e1, Nat.card_congr e2, Nat.card_eq_finsetCard,
    ← Nat.count_eq_card_filter_range]
  unfold fi23Common Nat.count
  exact List.countP_congr fun i _ => by simp [Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem fi23_case
    {R : Table} {r : Fi23.J} (hR : Rep 31671 R r) {e₀ e₁ e₂ : ℕ}
    {o₀ o₁ o₂ : Bool} (h : fi23CaseOK Fi23.orb R e₀ e₁ e₂ o₀ o₁ o₂ = true) :
    ∃ c₀ c₁ c₂ : Fi23.J, c₀ * r = r * c₀ ∧ c₁ * r = r * c₁ ∧ c₂ * r = r * c₂ ∧
      Nat.card {x : Fi23.D23 // r * x * r⁻¹ = x ∧ ⁅c₁, c₀⁆ * x * ⁅c₁, c₀⁆⁻¹ = x ∧
        ⁅c₂, c₀⁆ * x * ⁅c₂, c₀⁆⁻¹ = x} = 2 := by
  unfold fi23CaseOK fi23WitOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hG0, hC0⟩, hc0⟩, ⟨⟨hG1, hC1⟩, hc1⟩⟩, ⟨⟨hG2, hC2⟩, hc2⟩⟩, hcount⟩ := h
  have hw : ∀ w : List ℤ, Rep 31671 (wordT 31671 (genTables Fi23.orb) w) (wordG Fi23.genG w) :=
    fun w => Rep.wordT (by norm_num) w fun l _ => Fi23.rep_gen l
  have hwit : ∀ (w : List ℤ) (e : ℕ) (o : Bool),
      invOK 31671 (wordT 31671 (genTables Fi23.orb) w)
        (invT 31671 (wordT 31671 (genTables Fi23.orb) w)) = true →
      Rep 31671 (fi23CT Fi23.orb R w e o) (fi23Bray r (wordG Fi23.genG w) e o) := by
    intro w e o hinv
    exact rep_fi23BrayT hR (hw w) (Rep.inv_of_invOK (hw w) hinv) e o
  have hcomm : ∀ {C : Table} {c : Fi23.J}, Rep 31671 C c →
      compT 31671 C R = compT 31671 R C → c * r = r * c := fun {C c} hC e => by
    have h2 : Rep 31671 (compT 31671 C R) (r * c) := by
      rw [e]
      exact Rep.compT hR hC
    exact Fi23.rep_unique (Rep.compT hC hR) h2
  have r0 := hwit fi23W0 e₀ o₀ hG0
  have r1 := hwit fi23W1 e₁ o₁ hG1
  have r2 := hwit fi23W2 e₂ o₂ hG2
  refine ⟨_, _, _, hcomm r0 hc0, hcomm r1 hc1, hcomm r2 hc2, ?_⟩
  have i0 := Rep.inv_of_invOK r0 hC0
  have i1 := Rep.inv_of_invOK r1 hC1
  have i2 := Rep.inv_of_invOK r2 hC2
  have hE1 := Rep.compT r1 (Rep.compT r0 (Rep.compT i1 i0))
  have hE2 := Rep.compT r2 (Rep.compT r0 (Rep.compT i2 i0))
  rw [← mul_assoc, ← mul_assoc, ← commutatorElement_def] at hE1 hE2
  rw [card_fixed3_eq hR hE1 hE2]
  exact hcount

theorem oddCore_centralizer_of_fixed_data {G : Type*} [Group G] [Finite G] {E : Set G}
    (hE : ∀ g x : G, x ∈ E → g * x * g⁻¹ ∈ E) {r : G}
    (hstab : ∀ x ∈ E, x * r = r * x →
      CFSG.oddCore ↥(Subgroup.centralizer {x} ⊓ Subgroup.centralizer {r}) = ⊥) {n q : ℕ}
    (hn : Nat.card {x : E // r * x * r⁻¹ = x} = n) (hq : Nat.gcd n (Nat.card G) = q)
    (hq' : q = 1 ∨ (q.Prime ∧ q ≠ 2))
    (hwit : q ≠ 1 → ∃ c₀ c₁ c₂ : G, c₀ * r = r * c₀ ∧ c₁ * r = r * c₁ ∧
      c₂ * r = r * c₂ ∧ Nat.card {x : E // r * x * r⁻¹ = x ∧
        ⁅c₁, c₀⁆ * x * ⁅c₁, c₀⁆⁻¹ = x ∧ ⁅c₂, c₀⁆ * x * ⁅c₂, c₀⁆⁻¹ = x} = 2) :
    CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set G)) = ⊥ := by
  set C := Subgroup.centralizer ({r} : Set G)
  set V := CFSG.oddCore C
  have hfix : ∀ {x : G}, r * x * r⁻¹ = x → x * r = r * x := fun {x} h => by
    calc x * r = r * x * r⁻¹ * r := by rw [h]
      _ = r * x := by group
  have hVr : ∀ v ∈ V, ∀ x : G, r * x * r⁻¹ = x →
      r * ((v : G) * x * (v : G)⁻¹) * r⁻¹ = (v : G) * x * (v : G)⁻¹ :=
    fun v _ x h => conj_fix_of_commute (Subgroup.mem_centralizer_singleton_iff.1 v.2) h
  have hdvd1 : Nat.card V ∣ n := by
    rw [← hn]
    exact card_oddCore_dvd hE (fun x => r * x * r⁻¹ = x) (fun x h => hfix h) hstab hVr
  have hdvd2 : Nat.card V ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card V).trans (Subgroup.card_subgroup_dvd_card C)
  have hdvd : Nat.card V ∣ q := by
    rw [← hq]
    exact Nat.dvd_gcd hdvd1 hdvd2
  rw [← Subgroup.card_eq_one]
  rcases hq' with rfl | ⟨hqp, hq2⟩
  · exact Nat.dvd_one.1 hdvd
  rcases (Nat.dvd_prime hqp).1 hdvd with h1 | hVq
  · exact h1
  exfalso
  obtain ⟨c₀, c₁, c₂, h₀, h₁, h₂, hcard⟩ := hwit hqp.ne_one
  have : Fact q.Prime := ⟨hqp⟩
  have hcyc : IsCyclic V := isCyclic_of_prime_card hVq
  have hcen :=
    CFSG.ComponentClassification.LiteratureLocal.commutator_le_centralizer_of_conj_mem_zpowers
      (X := ⊤) (CFSG.oddCore_normal (G := C)) fun x _ v hv =>
        CFSG.ComponentClassification.LiteratureLocal.conj_mem_zpowers_of_isCyclic
          (CFSG.oddCore_normal (G := C)) hcyc x hv
  set c₀' : C := ⟨c₀, Subgroup.mem_centralizer_singleton_iff.2 h₀⟩
  have hc : ∀ c : C, ∀ v ∈ V, (v : G) * ⁅(c : G), c₀⁆ = ⁅(c : G), c₀⁆ * (v : G) := by
    intro c v hv
    have hm := Subgroup.mem_centralizer_iff.1
      (hcen (Subgroup.commutator_mem_commutator (Subgroup.mem_top c) (Subgroup.mem_top c₀')))
      v hv
    exact congrArg Subtype.val hm
  have hc1 := hc ⟨c₁, Subgroup.mem_centralizer_singleton_iff.2 h₁⟩
  have hc2 := hc ⟨c₂, Subgroup.mem_centralizer_singleton_iff.2 h₂⟩
  have hdvd3 := card_oddCore_dvd hE (fun x => r * x * r⁻¹ = x ∧
      ⁅c₁, c₀⁆ * x * ⁅c₁, c₀⁆⁻¹ = x ∧ ⁅c₂, c₀⁆ * x * ⁅c₂, c₀⁆⁻¹ = x)
    (fun x h => hfix h.1) hstab fun v hv x h =>
      ⟨hVr v hv x h.1, conj_fix_of_commute (hc1 v hv) h.2.1,
        conj_fix_of_commute (hc2 v hv) h.2.2⟩
  rw [hcard, hVq] at hdvd3
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd3 with h | h
  · exact hqp.ne_one h
  · exact hq2 h

theorem oddCore_centralizer_of_witness
    {r : Fi23.J} (hr : r ^ 2 = 1) {n q : ℕ}
    (hn : Nat.card {x : Fi23.D23 // r * x * r⁻¹ = x} = n)
    (hq : Nat.gcd n 4089470473293004800 = q) (hq' : q = 1 ∨ (q.Prime ∧ q ≠ 2))
    (hwit : q ≠ 1 → ∃ c₀ c₁ c₂ : Fi23.J, c₀ * r = r * c₀ ∧ c₁ * r = r * c₁ ∧
      c₂ * r = r * c₂ ∧ Nat.card {x : Fi23.D23 // r * x * r⁻¹ = x ∧
        ⁅c₁, c₀⁆ * x * ⁅c₁, c₀⁆⁻¹ = x ∧ ⁅c₂, c₀⁆ * x * ⁅c₂, c₀⁆⁻¹ = x} = 2) :
    CFSG.oddCore ↥(Subgroup.centralizer ({r} : Set Fi23.J)) = ⊥ :=
  @oddCore_centralizer_of_fixed_data Fi23.J inferInstance inferInstance Fi23.D23
    (fun g x hx => Fi23.conj_mem_D23 g x hx) r
    (fun x hx hxr => oddCore_inf_centralizer_J hx hxr.symm hr) n q hn
    (by rw [Fi23.card_J]; exact hq) hq' hwit

theorem oddCore_centralizer_J
    (t : Fi23.J) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set Fi23.J)) = ⊥ := by
  have h2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have h1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by decide)
  have hcert : fi23WitChecks Fi23.orb = true := fi23Wit_certificate
  unfold fi23WitChecks at hcert
  simp only [Bool.and_eq_true] at hcert
  rcases Fi23.involution_cover t h2 h1 with h | h | h
  · refine oddCore_centralizer_eq_bot_of_isConj h (oddCore_centralizer_of_witness Fi23.d_sq'
      Fi23.card_fixed_d (by norm_num) (Or.inl rfl) fun h => absurd rfl h)
  · refine oddCore_centralizer_eq_bot_of_isConj h (oddCore_centralizer_of_witness
      Fi23.d_mul_d1_sq Fi23.card_fixed_d_mul_d1 (q := 5) (by norm_num)
      (Or.inr ⟨by norm_num, by norm_num⟩) fun _ => fi23_case Fi23.rep_XBT hcert.1.1)
  · refine oddCore_centralizer_eq_bot_of_isConj h (oddCore_centralizer_of_witness
      Fi23.t2_sq Fi23.card_fixed_t2 (q := 3) (by norm_num)
      (Or.inr ⟨by norm_num, by norm_num⟩) fun _ => fi23_case Fi23.rep_XCT hcert.1.2)

@[expose] noncomputable def fi23U2 : Fi23.J :=
  Fi23.d * (Fi23.genG 1 * (Fi23.d * Fi23.genG (-1)))

@[expose] noncomputable def fi23U3 : Fi23.J :=
  fi23U2 * (wordG Fi23.genG fi23WordW * (Fi23.d * (wordG Fi23.genG fi23WordW)⁻¹))

theorem fi23Rep_parts : fi23RepOK Fi23.orb = true := by
  have hcert : fi23WitChecks Fi23.orb = true := fi23Wit_certificate
  unfold fi23WitChecks at hcert
  simp only [Bool.and_eq_true] at hcert
  exact hcert.2

theorem rep_fi23U2 : Rep 31671 (fi23U2T Fi23.orb) fi23U2 :=
  Rep.compT Fi23.rep_dTab (Rep.compT (Fi23.rep_gen 1) (Rep.compT Fi23.rep_dTab (Fi23.rep_gen (-1))))

theorem rep_fi23U3 :
    Rep 31671 (fi23U3T Fi23.orb) fi23U3 := by
  have h := fi23Rep_parts
  unfold fi23RepOK at h
  simp only [Bool.and_eq_true] at h
  have hW : Rep 31671 (wordT 31671 (genTables Fi23.orb) fi23WordW) (wordG Fi23.genG fi23WordW) :=
    Rep.wordT (by norm_num) _ fun l _ => Fi23.rep_gen l
  exact Rep.compT rep_fi23U2 (Rep.compT hW (Rep.compT Fi23.rep_dTab
    (Rep.inv_of_invOK hW h.1.1.1.1.1.1)))

theorem fi23_inv_facts {T : Table} {u : Fi23.J} (hT : Rep 31671 T u)
    (h1 : compT 31671 T T = idT 31671) (h2 : isIdT T = false) :
    u ^ 2 = 1 ∧ u ≠ 1 := by
  refine ⟨?_, Fi23.ne_one_of_isIdT hT h2⟩
  rw [sq]
  exact Fi23.rep_unique (h1 ▸ Rep.compT hT hT) (Rep.idT (by norm_num))

theorem isConj_fi23U2_fi23U3 :
    IsConj (Fi23.d * Fi23.d1) fi23U2 ∧ IsConj Fi23.t2 fi23U3 := by
  have h := fi23Rep_parts
  unfold fi23RepOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨-, h2a⟩, h2b⟩, h2c⟩, h3a⟩, h3b⟩, h3c⟩ := h
  obtain ⟨h2s, h21⟩ := fi23_inv_facts rep_fi23U2 h2a h2b
  obtain ⟨h3s, h31⟩ := fi23_inv_facts rep_fi23U3 h3a h3b
  have hc2 : Nat.card {x : Fi23.D23 // fi23U2 * x * fi23U2⁻¹ = x} = 695 := by
    rw [Fi23.card_fixed_eq rep_fi23U2]; exact h2c
  have hc3 : Nat.card {x : Fi23.D23 // fi23U3 * x * fi23U3⁻¹ = x} = 183 := by
    rw [Fi23.card_fixed_eq rep_fi23U3]; exact h3c
  constructor
  · rcases Fi23.involution_cover _ h2s h21 with h | h | h
    · have := Fi23.card_fixed_conj h
      rw [Fi23.card_fixed_d, hc2] at this
      exact absurd this (by decide)
    · exact h
    · have := Fi23.card_fixed_conj h
      rw [Fi23.card_fixed_t2, hc2] at this
      exact absurd this (by decide)
  · rcases Fi23.involution_cover _ h3s h31 with h | h | h
    · have := Fi23.card_fixed_conj h
      rw [Fi23.card_fixed_d, hc3] at this
      exact absurd this (by decide)
    · have := Fi23.card_fixed_conj h
      rw [Fi23.card_fixed_d_mul_d1, hc3] at this
      exact absurd this (by decide)
    · exact h

theorem fi23U2_facts :
    fi23U2 ^ 2 = 1 ∧ fi23U2 ≠ 1 := by
  have h := fi23Rep_parts
  unfold fi23RepOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  exact fi23_inv_facts rep_fi23U2 h.1.1.1.1.1.2 h.1.1.1.1.2

theorem fi23U3_facts :
    fi23U3 ^ 2 = 1 ∧ fi23U3 ≠ 1 := by
  have h := fi23Rep_parts
  unfold fi23RepOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  exact fi23_inv_facts rep_fi23U3 h.1.1.2 h.1.2

theorem fi23_involution_class
    (g : Fi23.J) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    IsConj Fi23.d g ∨ IsConj fi23U2 g ∨ IsConj fi23U3 g := by
  rcases Fi23.involution_cover g hg2 hg1 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (isConj_fi23U2_fi23U3.1.symm.trans h))
  · exact Or.inr (Or.inr (isConj_fi23U2_fi23U3.2.symm.trans h))

theorem CTUC_Fi23_all_involution_centralizers_odd_core_trivial :
    ∀ t : Blueprint.NativeSporadic.Fi23, orderOf t = 2 →
      CFSG.oddCore ↥(Subgroup.centralizer ({t} : Set Blueprint.NativeSporadic.Fi23)) = ⊥ := by
  intro t ht
  have ho : orderOf (Fi23.fi23EquivJ t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact ht
  have h := @oddCore_centralizer_eq_bot_of_mulEquiv Fi23.J Blueprint.NativeSporadic.Fi23
    Fi23.J.toGroup Units.instGroup Fi23.fi23EquivJ.symm _ (oddCore_centralizer_J _ ho)
  rwa [MulEquiv.symm_apply_apply] at h

end CFSG.Sporadic.FischerOddCore
