module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs522One
public import CFSG.Quasithin.Vol2.Ch5Sec1L34V2
public import CFSG.Quasithin.Vol2.Ch5ModulesFFOrd
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs522

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section General

variable {G : Type} [Group G] [Finite G]

theorem conj_eq_of_odd_of_card_three {D₃ : Subgroup G} (h3 : Nat.card D₃ = 3) {b : G}
    (hb : b ∈ Subgroup.normalizer (D₃ : Set G)) (hodd : Odd (orderOf b)) {d : G} (hd : d ∈ D₃) :
    b * d * b⁻¹ = d := by
  by_cases hd1 : d = 1
  · rw [hd1, mul_one, mul_inv_cancel]
  have hbd : b * d * b⁻¹ ∈ D₃ := (Subgroup.mem_normalizer_iff.mp hb d).mp hd
  have hd3 : d ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥D₃) (x := ⟨d, hd⟩)
    rw [h3] at h
    exact congrArg Subtype.val h
  rcases eq_one_or_eq_or_eq_sq_of_card_three h3 hd hd1 hbd with h1 | h1 | h1
  · exfalso
    apply hd1
    have : d = b⁻¹ * (b * d * b⁻¹) * b := by group
    rw [this, h1]; group
  · exact h1
  · exfalso
    have key : ∀ k : ℕ, b ^ k * d * (b ^ k)⁻¹ = d ^ 2 ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc b ^ (k + 1) * d * (b ^ (k + 1))⁻¹ = b ^ k * (b * d * b⁻¹) * (b ^ k)⁻¹ := by
              rw [pow_succ]; group
          _ = (b ^ k * d * (b ^ k)⁻¹) ^ 2 := by rw [h1, conj_pow]
          _ = d ^ 2 ^ (k + 1) := by rw [ih, ← pow_mul, pow_succ]
    have h := key (orderOf b)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h
    obtain ⟨m, hm⟩ := hodd
    have h2 : 2 ^ orderOf b % 3 = 2 := by
      rw [hm, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h4 : d ^ 2 ^ orderOf b = d ^ 2 := by
      rw [← Nat.mod_add_div (2 ^ orderOf b) 3, h2, pow_add, pow_mul, hd3, one_pow, mul_one]
    rw [h4] at h
    apply hd1
    calc d = d ^ 2 * d⁻¹ := by group
      _ = d * d⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel d

theorem eq_of_le_of_odd_relIndex {C P Y : Subgroup G} (hPC : P ≤ C) (hYP : Y ≤ P)
    (hCY : C ≤ Subgroup.normalizer (Y : Set G)) (h2 : ∀ x ∈ C, ∃ a : ℕ, x ^ 2 ^ a ∈ Y)
    (hodd : Odd (P.relIndex C)) : P = C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYC : Y ≤ C := hYP.trans hPC
  set Y' := Y.subgroupOf C with hY'
  have : Y'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYC).mpr hCY
  have hQ : IsPGroup 2 (↥C ⧸ Y') := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨a, ha⟩ := h2 x x.2
      refine ⟨a, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hY', Subgroup.mem_subgroupOf]
      simpa using ha
  set P' := P.subgroupOf C with hP'
  have hYP' : Y' ≤ P' := fun x hx => hYP hx
  have hidx : (P'.map (QuotientGroup.mk' Y')).index = P'.index :=
    P'.index_map_eq (QuotientGroup.mk'_surjective Y') (by rw [QuotientGroup.ker_mk']; exact hYP')
  obtain ⟨k, hk⟩ := hQ.index (P'.map (QuotientGroup.mk' Y'))
  rw [hidx] at hk
  have hk' : P.relIndex C = 2 ^ k := hk
  have hk0 : k = 0 := by
    by_contra hk0
    rw [hk'] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
  rw [hk0, pow_zero, Subgroup.relIndex_eq_one] at hk'
  exact le_antisymm hPC hk'

end General

section Setting

variable {G : Type} [Group G] [Finite G]

namespace Hyp5_1_8

variable {T M L H B D : Subgroup G} {n : ℕ}

theorem card_inf_eq (hyp : Hyp5_1_8 G T M L H n) (hN : IsNotation5_1_9 T M L H B D) :
    Nat.card ↥(M ⊓ H) = Nat.card T * Nat.card B := by
  have hh := hyp.toHyp5_0_1
  have hTMH : T ≤ M ⊓ H := le_inf hh.T_le hyp.hStar.1.1
  have hSylMH : IsSylowTwoOf T (M ⊓ H) := hh.isSylowTwoOf hTMH
  obtain ⟨hBle, hBodd, k, hk⟩ := hN.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hSylMH.2.1
  have e1 := B.relIndex_mul_card (M ⊓ H)
  rw [inf_eq_left.mpr hBle, hk] at e1
  have e2 := T.relIndex_mul_card (M ⊓ H)
  rw [inf_eq_left.mpr hTMH, hm] at e2
  have hodd2 : Odd (T.relIndex (M ⊓ H)) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSylMH.2.2)
  obtain ⟨hkm, -⟩ := two_pow_mul_odd_inj (a := k) (b := m) hBodd hodd2
    (by rw [e1, ← e2, mul_comm])
  rw [← e1, hkm, hm]

theorem exists_mul_eq_of_mem_inf (hyp : Hyp5_1_8 G T M L H n) (hN : IsNotation5_1_9 T M L H B D)
    {x : G} (hx : x ∈ M ⊓ H) : ∃ t ∈ T, ∃ b ∈ B, t * b = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := hyp.toHyp5_0_1
  have hTMH : T ≤ M ⊓ H := le_inf hh.T_le hyp.hStar.1.1
  obtain ⟨hBle, hBodd, -⟩ := hN.1
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hh.sylow.1
  have hTB : T ⊓ B = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hBodd)
  let f : ↥T × ↥B → ↥(M ⊓ H) :=
    fun p => ⟨(p.1 : G) * p.2, (M ⊓ H).mul_mem (hTMH p.1.2) (hBle p.2.2)⟩
  have hfi : Function.Injective f := by
    rintro ⟨t, b⟩ ⟨t', b'⟩ h
    have h1 : (t : G) * b = t' * b' := congrArg Subtype.val h
    have h2 : (t' : G)⁻¹ * t = b' * (b : G)⁻¹ := by
      calc (t' : G)⁻¹ * t = (t' : G)⁻¹ * (t * b) * (b : G)⁻¹ := by group
        _ = (t' : G)⁻¹ * (t' * b') * (b : G)⁻¹ := by rw [h1]
        _ = b' * (b : G)⁻¹ := by group
    have hmem : (t' : G)⁻¹ * t ∈ T ⊓ B :=
      ⟨T.mul_mem (T.inv_mem t'.2) t.2, by rw [h2]; exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hTB, Subgroup.mem_bot] at hmem
    have ht : (t : G) = t' := by
      have : (t : G) = t' * ((t' : G)⁻¹ * t) := by group
      rw [this, hmem, mul_one]
    have hb : (b : G) = b' := by
      rw [ht] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext ht) (Subtype.ext hb)
  have hfb : Function.Bijective f :=
    hfi.bijective_of_nat_card_le (by rw [Nat.card_prod, hyp.card_inf_eq hN])
  obtain ⟨⟨t, b⟩, hp⟩ := hfb.2 ⟨x, hx⟩
  exact ⟨t, t.2, b, b.2, congrArg Subtype.val hp⟩

end Hyp5_1_8

namespace Setup521

variable {T M L V H B D D₃ Z₁ : Subgroup G} {n : ℕ}
variable (s : Setup521 G T M L V H B D D₃ Z₁ n)
include s

theorem B_le_centralizer (h5114 : Stmt5_1_14_first) (hF : L2TorusFact) :
    B ≤ Subgroup.centralizer (conjClosure Z₁ D₃ : Set G) := by
  have hh := s.hyp.hyp.toHyp5_0_1
  have hN := s.hyp.notation59
  have hBMH : B ≤ M ⊓ H := hN.1.1
  have hHZ : H ≤ Subgroup.centralizer (Z₁ : Set G) := by
    have hZH := (h5114 G T M L V H B D n s.hyp.hyp hN s.hyp.module s.hyp.l34).2.1.1
    have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (H : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hZC (s.Z₁_le_Z hy)) x hx).symm
  obtain ⟨hcyc, -⟩ := hh.isCyclic_card_of_isHall hF hN.2.1
  have hBD₃ : ∀ b ∈ B, b ∈ Subgroup.normalizer (D₃ : Set G) := by
    intro b hb
    have hbD : b ∈ Subgroup.normalizer (D : Set G) := hN.2.2 hb
    set D₃' := D₃.map (MulAut.conj b).toMonoidHom with hD₃'
    have hD₃'D : D₃' ≤ D := by
      rintro _ ⟨d, hd, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hbD d).mp (s.le_D hd)
    have hcard' : Nat.card D₃' = 3 := by
      rw [hD₃', Subgroup.card_map_of_injective (MulAut.conj b).injective, s.card_D₃]
    have heq : D₃'.subgroupOf D = D₃.subgroupOf D := by
      rw [IsCyclic.subgroup_eq_iff_card_eq,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₃'D).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe s.le_D).toEquiv, hcard', s.card_D₃]
    have heq' : D₃' = D₃ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hD₃'D, ← Subgroup.map_subgroupOf_eq_of_le s.le_D,
        heq]
    apply mem_normalizer_of_forall_conj_mem'
    intro d hd
    rw [← heq']
    exact ⟨d, hd, rfl⟩
  have hBodd : ∀ b ∈ B, Odd (orderOf b) := by
    intro b hb
    have h1 : orderOf b ∣ Nat.card B := by
      rw [← Subgroup.orderOf_mk b hb]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hN.1.2.1 h1
  intro b hb
  have hV₂B : conjClosure Z₁ D₃ ≤ Subgroup.centralizer (B : Set G) := by
    refine conjClosure_le fun d hd z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcd : c * d * c⁻¹ = d :=
      conj_eq_of_odd_of_card_three s.card_D₃ (hBD₃ c hc) (hBodd c hc) hd
    have hcz : c * z * c⁻¹ = z := by
      have h1 : c * z = z * c := (Subgroup.mem_centralizer_iff.mp
        (hHZ (hBMH hc).2) z hz).symm
      rw [h1, mul_assoc, mul_inv_cancel, mul_one]
    calc c * (d * z * d⁻¹) = (c * d * c⁻¹) * (c * z * c⁻¹) * (c * d * c⁻¹)⁻¹ * c := by group
      _ = d * z * d⁻¹ * c := by rw [hcd, hcz]
  exact Subgroup.le_centralizer_iff.mp hV₂B hb

end Setup521

theorem stmt5_1_22_one_of_inputs (h5114 : Stmt5_1_14_first) (hF : L2TorusFact)
    (h520 : Stmt5_1_20) (hY : Stmt5_1_22_one_Y) (hX : Stmt5_1_22_one_X) : Stmt5_1_22_one := by
  intro G _ _ T M L V H B D D₃ Z₁ n hyp hN hV hK h4 hD₃ h3 hZ₁
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Hyp5_1_14 G T M L V H B D n := ⟨hyp, hN, hV, hK⟩
  have hh := hyp.toHyp5_0_1
  have s : Setup521 G T M L V H B D D₃ Z₁ n :=
    ⟨h, hD₃, h3, (h520 G T M L V H B D n hyp hN hV hK h4 D₃ hD₃ h3).1, hZ₁⟩
  set V₂ := conjClosure Z₁ D₃ with hV₂def
  set C := Subgroup.centralizer (V₂ : Set G) with hCdef
  have hBC : B ≤ C := s.B_le_centralizer h5114 hF
  have hTV₂ := s.T_le_normalizer_V₂ hF
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := by
    intro t ht
    apply mem_normalizer_of_forall_conj_mem'
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : t⁻¹ * v * t ∈ V₂ := by
      have := (Subgroup.mem_normalizer_iff.mp (hTV₂ (T.inv_mem ht)) v).mp hv
      simpa using this
    have hc' := hc _ hv'
    calc v * (t * c * t⁻¹) = t * ((t⁻¹ * v * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * v * t)) * t⁻¹ := by rw [hc']
      _ = t * c * t⁻¹ * v := by group
  have hSyl : IsSylowTwoOf (T ⊓ C) C :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf (le_sup_right : T ≤ C ⊔ T)) le_sup_left
      (sup_le Subgroup.le_normalizer hTC)
  set P := (T ⊓ C) ⊔ B with hPdef
  have hPC : P ≤ C := sup_le inf_le_right hBC
  have hYP := hY G T M L V H B D D₃ Z₁ n hyp hN hV hK h4 hD₃ h3 hZ₁
  have hCY : C ≤ Subgroup.normalizer (oThreePrimeResidual C : Set G) := by
    rw [oThreePrimeResidual, Subgroup.le_normalizer_closure_iff]
    rintro c hc g ⟨hg, k, hk⟩
    refine Subgroup.subset_closure ⟨C.mul_mem (C.mul_mem hc hg) (C.inv_mem hc), k, ?_⟩
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  have h2Y : ∀ x ∈ C, ∃ a : ℕ, x ^ 2 ^ a ∈ oThreePrimeResidual C := by
    intro x hx
    obtain ⟨a, b, hab⟩ := hX G T M L V H B D D₃ Z₁ n hyp hN hV hK h4 hD₃ h3 hZ₁ x hx
    refine ⟨a, Subgroup.subset_closure ⟨C.pow_mem hx _, b, ?_⟩⟩
    rw [← pow_mul, hab]
  have hodd : Odd (P.relIndex C) := by
    have hdvd := Subgroup.relIndex_dvd_of_le_left (L := C) (le_sup_left : T ⊓ C ≤ P)
    refine Odd.of_dvd_nat ?_ hdvd
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hSyl.2.2)
  have hPeq : P = C := eq_of_le_of_odd_relIndex hPC hYP hCY h2Y hodd
  have hTMH : T ≤ M ⊓ H := le_inf hh.T_le hyp.hStar.1.1
  have hCMH : C ≤ M ⊓ H := hPeq ▸ sup_le (inf_le_left.trans hTMH) hN.1.1
  refine ⟨?_, hCMH.trans inf_le_left⟩
  ext c
  constructor
  · rintro ⟨t, ht, b, hb, rfl⟩
    exact C.mul_mem ht.2 (hBC hb)
  · intro hc
    obtain ⟨t, ht, b, hb, rfl⟩ := hyp.exists_mul_eq_of_mem_inf hN (hCMH hc)
    have htC : t ∈ C := by
      have := C.mul_mem hc (C.inv_mem (hBC hb))
      simpa using this
    exact ⟨t, ⟨ht, htC⟩, b, hb, rfl⟩

end Setting

end CFSG.Quasithin.H13
