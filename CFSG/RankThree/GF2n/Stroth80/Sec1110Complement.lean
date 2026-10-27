module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110DualAct

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.SpecialLinear
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
variable {n : ℕ} {X₁ X₂ : Subgroup G}

theorem exists_conj_complement (hc : Ctx M Q Z B) (hw : Width Q Z n) (hn : 3 ≤ n)
    (hD : GlobalModelData M Q Z γ M₀)
    (hZ : Z ≤ X₂) (hXQ : X₂ ≤ Q) (hX₁ : X₁ = Z)
    (nat2 : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁
      (Q)) :
    ∃ x ∈ M, X₂ ⊓ conjSubgroup x X₂ = Z ∧ X₂ ⊔ conjSubgroup x X₂ = Q := by
  have hX₂ab : IsMulCommutative X₂ := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hcommZ : ⁅(a : G), (b : G)⁆ ∈ Z := M₀.comm_mem (a : G) (hXQ a.2) (b : G) (hXQ b.2)
    have hB := B_vanishes_on_X₂_of_naturalRep (M₀ := M₀) hn hX₁ hXQ nat2 hc hD
      (a : G) a.2 (b : G) b.2
    have hγ : γ ⁅(a : G), (b : G)⁆ = 0 := by
      rw [M₀.comm_eq (a : G) (hXQ a.2) (b : G) (hXQ b.2), hB]
    exact commutatorElement_eq_one_iff_mul_comm.mp (hD.reg.inj _ hcommZ hγ)
  have hK2 : 2 ≤ Nat.card K := by
    have := hc.hyp.q4
    rw [← hD.card] at this
    omega
  have hX₂ne : X₂ ≠ Z := by
    intro hEq
    have hcardq := card_quotient_X₂_X₁ (K := K) (m := n) nat2
    have htop : X₁.subgroupOf X₂ = ⊤ := by
      rw [hEq, hX₁]
      exact Subgroup.subgroupOf_self Z
    have hq1 : Nat.card (↥X₂ ⧸ X₁.subgroupOf X₂) = 1 := by
      rw [htop]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
    rw [hq1] at hcardq
    have hpow : 1 < Nat.card K ^ n :=
      one_lt_pow' (by omega : 1 < Nat.card K) (by omega : n ≠ 0)
    omega
  have hex : ∃ x ∈ M, conjSubgroup x X₂ ≠ X₂ := by
    by_contra h
    push Not at h
    have hnorm : M ≤ Subgroup.normalizer (X₂ : Set G) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      simpa [conjSubgroup] using h m hm
    have hX₂M : X₂ ≤ M := hXQ.trans hc.hyp.Q_normal.1
    have hP : (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
        IsMulCommutative U) X₂ := ⟨hX₂M, hnorm, hX₂ab⟩
    exact hX₂ne (hc.hyp.maxAb.eq_of_le hP hZ).symm
  obtain ⟨x, hxM, hxne⟩ := hex
  let W : Subgroup G := conjSubgroup x X₂
  have hWne : W ≠ X₂ := hxne
  have hWQ : W ≤ Q := by
    calc W = conjSubgroup x X₂ := rfl
      _ ≤ conjSubgroup x Q := Subgroup.map_mono hXQ
      _ = Q := hc.conj_Q_eq hxM
  have hZW : Z ≤ W := by
    calc Z = conjSubgroup x Z := (hc.conj_Z_eq hxM).symm
      _ ≤ conjSubgroup x X₂ := Subgroup.map_mono hZ
      _ = W := rfl
  have hcardW : Nat.card W = Nat.card X₂ := card_conjSubgroup x X₂
  let A : Subgroup G := X₂ ⊓ W
  have hZ_le_A : Z ≤ A := by
    intro z hz
    exact ⟨hZ hz, hZW hz⟩
  have hA_le_X₂ : A ≤ X₂ := inf_le_left
  have nat2keep : NaturalRep (ι := Fin n) K (StatedSL n K) (XbarPre M Q Z B) X₂ X₁
      (Q) := nat2
  obtain ⟨φ, hrange, -, hnormX₂, hN, ψ, hψ⟩ := nat2
  haveI := hN
  let S : AddSubgroup (Fin n → K) :=
    { carrier := {u | ∃ a : ↥X₂, (a : G) ∈ A ∧
        Multiplicative.toAdd (ψ (QuotientGroup.mk a)) = u},
      add_mem' := by
        rintro u v ⟨a, haA, rfl⟩ ⟨b, hbA, rfl⟩
        refine ⟨a * b, A.mul_mem haA hbA, ?_⟩
        rw [QuotientGroup.mk_mul, map_mul, toAdd_mul]
      zero_mem' := by
        refine ⟨1, A.one_mem, ?_⟩
        rw [QuotientGroup.mk_one, map_one, toAdd_one]
      neg_mem' := by
        rintro u ⟨a, haA, rfl⟩
        refine ⟨a⁻¹, A.inv_mem haA, ?_⟩
        rw [QuotientGroup.mk_inv, map_inv, toAdd_inv] }
  have hXbarPre_normW : ∀ s ∈ XbarPre M Q Z B, conjSubgroup (s : G) W = W := by
    intro s hs
    have hxsx : x⁻¹ * (s : G) * x ∈ XbarPre M Q Z B := by
      have hmem : (s : G) ∈ conjSubgroup x (XbarPre M Q Z B) := by
        rw [XbarPre_normal hc hxM]
        exact hs
      exact mem_conjSubgroup.mp hmem
    have hnorm : conjSubgroup (x⁻¹ * (s : G) * x) X₂ = X₂ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hnormX₂ hxsx)
    calc conjSubgroup (s : G) W
        = conjSubgroup (s : G) (conjSubgroup x X₂) := rfl
      _ = conjSubgroup ((s : G) * x) X₂ := conjSubgroup_conjSubgroup (s : G) x X₂
      _ = conjSubgroup x (conjSubgroup (x⁻¹ * (s : G) * x) X₂) := by
          rw [conjSubgroup_conjSubgroup x (x⁻¹ * (s : G) * x) X₂]
          congr 1
          group
      _ = conjSubgroup x X₂ := by rw [hnorm]
      _ = W := rfl
  have hSinv : ∀ g ∈ StatedSL n K, ∀ u ∈ S,
      (g : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ S := by
    intro g hg u hu
    obtain ⟨a, haA, rfl⟩ := hu
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hg)
    have hsaX₂ : (s : G) * (a : G) * (s : G)⁻¹ ∈ X₂ :=
      (Subgroup.mem_normalizer_iff.mp (hnormX₂ s.2) (a : G)).mp a.2
    have hsaW : (s : G) * (a : G) * (s : G)⁻¹ ∈ W := by
      have haW : (a : G) ∈ W := haA.2
      have hmem : (s : G) * (a : G) * (s : G)⁻¹ ∈ conjSubgroup (s : G) W := by
        rw [mem_conjSubgroup]
        have h1 : (s : G)⁻¹ * ((s : G) * (a : G) * (s : G)⁻¹) * (s : G) = (a : G) := by
          group
        rwa [h1]
      rwa [hXbarPre_normW s s.2] at hmem
    refine ⟨⟨(s : G) * (a : G) * (s : G)⁻¹, hsaX₂⟩, ⟨hsaX₂, hsaW⟩, ?_⟩
    have hcoord := hψ s a ⟨(s : G) * (a : G) * (s : G)⁻¹, hsaX₂⟩ rfl
    rw [hcoord, hs]
  let W' : AddSubgroup ((Fin n → K) × (Fin n → K)) := S.prod ⊥
  have hW'inv : ∀ g ∈ StatedSL n K, ∀ p ∈ W',
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ p.1,
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ p.2) ∈ W' := by
    intro g hg p hp
    rw [AddSubgroup.mem_prod] at hp ⊢
    refine ⟨hSinv g hg p.1 hp.1, ?_⟩
    have hp2 : p.2 = 0 := AddSubgroup.mem_bot.mp hp.2
    simp [hp2]
  have hnpos : 0 < n := by omega
  let e : Fin n → K := Pi.single ⟨0, hnpos⟩ 1
  have he0 : e ≠ 0 := by
    intro h
    have h1 := congrFun h ⟨0, hnpos⟩
    simpa [e] using h1
  have hS_cases : S = ⊥ ∨ S = ⊤ := by
    rcases natDual_invariant_addSubgroup (K := K) hn W' hW'inv with h | h | h | h
    · left
      rw [AddSubgroup.eq_bot_iff_forall]
      intro v hv
      have hmemW : ((v, 0) : (Fin n → K) × (Fin n → K)) ∈ W' := by
        rw [show W' = S.prod ⊥ from rfl]
        exact AddSubgroup.mem_prod.mpr ⟨hv, by simp⟩
      rw [h] at hmemW
      have hzero := AddSubgroup.mem_bot.mp hmemW
      simpa using congrArg Prod.fst hzero
    · right
      rw [AddSubgroup.eq_top_iff']
      intro v
      have hmem : ((v, 0) : (Fin n → K) × (Fin n → K)) ∈ W' := by
        rw [h]
        exact AddSubgroup.mem_prod.mpr ⟨AddSubgroup.mem_top v, by simp⟩
      rw [AddSubgroup.mem_prod] at hmem
      exact hmem.1
    · exfalso
      have hmem : ((0, e) : (Fin n → K) × (Fin n → K)) ∈ W' := by
        rw [h]
        exact AddSubgroup.mem_prod.mpr ⟨by simp, AddSubgroup.mem_top e⟩
      rw [AddSubgroup.mem_prod] at hmem
      exact he0 (by simpa using hmem.2)
    · exfalso
      have hmem : ((0, e) : (Fin n → K) × (Fin n → K)) ∈ W' := by
        rw [h]
        exact AddSubgroup.mem_top _
      rw [AddSubgroup.mem_prod] at hmem
      exact he0 (by simpa using hmem.2)
  have hA_eq : A = Z := by
    rcases hS_cases with hSbot | hStop
    · refine le_antisymm ?_ hZ_le_A
      intro a ha
      have haX₂ : (a : G) ∈ X₂ := ha.1
      have hmemS : Multiplicative.toAdd (ψ (QuotientGroup.mk (⟨a, haX₂⟩ : ↥X₂))) ∈ S :=
        ⟨⟨a, haX₂⟩, ha, rfl⟩
      rw [hSbot] at hmemS
      rw [AddSubgroup.mem_bot] at hmemS
      have hψ1 : ψ (QuotientGroup.mk (⟨a, haX₂⟩ : ↥X₂)) = 1 :=
        Multiplicative.toAdd.injective (by simpa using hmemS)
      have hq1 : QuotientGroup.mk (⟨a, haX₂⟩ : ↥X₂) = 1 :=
        ψ.injective (by rw [hψ1, map_one])
      rw [QuotientGroup.eq_one_iff] at hq1
      rw [Subgroup.mem_subgroupOf, hX₁] at hq1
      exact hq1
    · exfalso
      have hX₂_le_A : X₂ ≤ A := by
        intro a ha
        have hmemS : Multiplicative.toAdd (ψ (QuotientGroup.mk (⟨a, ha⟩ : ↥X₂))) ∈ S := by
          rw [hStop]
          exact AddSubgroup.mem_top _
        obtain ⟨b, hbA, hbψ⟩ := hmemS
        have hψeq : ψ (QuotientGroup.mk b) =
            ψ (QuotientGroup.mk (⟨a, ha⟩ : ↥X₂)) :=
          Multiplicative.toAdd.injective hbψ
        have hclass : QuotientGroup.mk b = QuotientGroup.mk (⟨a, ha⟩ : ↥X₂) := ψ.injective hψeq
        have hmemX₁ : (b : G)⁻¹ * a ∈ X₁ := by
          have h := QuotientGroup.eq.mp hclass
          rwa [Subgroup.mem_subgroupOf] at h
        have hmemA : (b : G)⁻¹ * a ∈ A := by
          rw [hX₁] at hmemX₁
          exact hZ_le_A hmemX₁
        have heq : a = (b : G) * ((b : G)⁻¹ * a) := by group
        rw [heq]
        exact A.mul_mem hbA hmemA
      have hA_eq_X₂ : A = X₂ := le_antisymm hA_le_X₂ hX₂_le_A
      have hX₂_le_W : X₂ ≤ W := by
        intro a ha
        have haA : a ∈ A := by rwa [hA_eq_X₂]
        exact haA.2
      have hW_eq : W = X₂ :=
        (Subgroup.eq_of_le_of_card_ge hX₂_le_W (le_of_eq hcardW)).symm
      exact hWne hW_eq
  have huniq_img : M₀.img X₂ ⊓ M₀.img W = ⊥ := by
    rw [AddSubgroup.eq_bot_iff_forall]
    intro u hu
    obtain ⟨hu₂, huW⟩ := AddSubgroup.mem_inf.mp hu
    obtain ⟨a, haX₂, haQ, hae⟩ := M₀.mem_img.mp hu₂
    obtain ⟨b, hbW, hbQ, hbe⟩ := M₀.mem_img.mp huW
    have hbX₂ : b ∈ X₂ := by
      have hπ : M₀.π a = M₀.π b := hae.trans hbe.symm
      have hz : a⁻¹ * b ∈ Z := (M₀.pi_eq_iff haQ hbQ).mp hπ
      have heq : b = a * (a⁻¹ * b) := by group
      rw [heq]
      exact X₂.mul_mem haX₂ (hZ hz)
    have hbA : b ∈ A := ⟨hbX₂, hbW⟩
    have hbZ : b ∈ Z := hA_eq ▸ hbA
    rw [← hbe, (M₀.π_ker b hbQ).mpr hbZ]
  have hZpos : 0 < Nat.card Z := Nat.card_pos_iff.mpr ⟨⟨1⟩, Subtype.finite⟩
  have hcardX₂ : Nat.card ↥X₂ = Nat.card Z * Nat.card K ^ n :=
    card_X₂ (m := n) hX₁ (le_of_eq hX₁.symm) (by rw [hX₁]; exact hZ) nat2keep
  have hcardA₂ : Nat.card (M₀.img X₂) = Nat.card K ^ n := by
    have h1 := M₀.card_eq (S := X₂) hXQ hZ
    exact Nat.eq_of_mul_eq_mul_left hZpos (by rw [← h1, hcardX₂])
  have hcardW' : Nat.card ↥W = Nat.card Z * Nat.card K ^ n := by
    rw [hcardW, hcardX₂]
  have hcardAW : Nat.card (M₀.img W) = Nat.card K ^ n := by
    have h1 := M₀.card_eq (S := W) hWQ hZW
    exact Nat.eq_of_mul_eq_mul_left hZpos (by rw [← h1, hcardW'])
  have himgQ : M₀.img Q = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro u
    obtain ⟨q, hq, hu⟩ := M₀.π_surj u
    exact hu ▸ M₀.pi_mem_img hq hq
  have hcardE : Nat.card M₀.E = Nat.card K ^ (2 * n) := by
    have h1 := M₀.card_eq (S := Q) le_rfl hc.hyp.Z_normal.1
    rw [himgQ, AddSubgroup.card_top] at h1
    have hkey : Nat.card Z * Nat.card M₀.E = Nat.card Z * Nat.card Z ^ (2 * n) := by
      rw [← h1, hw, pow_succ']
    have hE : Nat.card M₀.E = Nat.card Z ^ (2 * n) :=
      Nat.eq_of_mul_eq_mul_left hZpos hkey
    rw [hE, ← hD.card]
  have hcard_mul : Nat.card (M₀.img X₂) * Nat.card (M₀.img W) = Nat.card M₀.E := by
    rw [hcardA₂, hcardAW, hcardE, ← pow_add, ← two_mul]
  have hEne : Nat.card M₀.E ≠ 0 := by
    rw [hcardE]
    exact pow_ne_zero _ (by omega : Nat.card K ≠ 0)
  haveI : Finite M₀.E := Nat.finite_of_card_ne_zero hEne
  have hinj : Function.Injective
      (fun p : (M₀.img X₂) × (M₀.img W) => (p.1 : M₀.E) + p.2) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hdiff : (a : M₀.E) - a' = (b' : M₀.E) - b := by
      rw [sub_eq_sub_iff_add_eq_add]
      simpa [add_comm] using hab
    have hleft : (a : M₀.E) - a' ∈ M₀.img X₂ := AddSubgroup.sub_mem _ a.2 a'.2
    have hright : (b' : M₀.E) - b ∈ M₀.img W := AddSubgroup.sub_mem _ b'.2 b.2
    have hmem : (a : M₀.E) - a' ∈ (⊥ : AddSubgroup M₀.E) := by
      rw [← huniq_img]
      exact AddSubgroup.mem_inf.mpr ⟨hleft, hdiff ▸ hright⟩
    rw [AddSubgroup.mem_bot] at hmem
    have ha : (a : M₀.E) = a' := sub_eq_zero.mp hmem
    have hb : (b : M₀.E) = b' := by
      have h0 : (b' : M₀.E) - b = 0 := by rw [← hdiff, ha, sub_self]
      exact (sub_eq_zero.mp h0).symm
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
  have hsurj : Function.Surjective
      (fun p : (M₀.img X₂) × (M₀.img W) => (p.1 : M₀.E) + p.2) := by
    have hbij := (Nat.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by rw [Nat.card_prod, hcard_mul]⟩
    exact hbij.2
  have hQ_le_sup : Q ≤ X₂ ⊔ W := by
    intro q hq
    obtain ⟨p, hp⟩ := hsurj (M₀.π q)
    obtain ⟨a, haX₂, haQ, haE⟩ := M₀.mem_img.mp p.1.2
    obtain ⟨b, hbW, hbQ, hbE⟩ := M₀.mem_img.mp p.2.2
    have hπeq : M₀.π (a * b) = M₀.π q := by
      rw [M₀.π_mul a haQ b hbQ, haE, hbE]
      exact hp
    have hz : (a * b)⁻¹ * q ∈ Z := (M₀.pi_eq_iff (Q.mul_mem haQ hbQ) hq).mp hπeq
    have heq : q = (a * b) * ((a * b)⁻¹ * q) := by group
    rw [heq]
    exact (X₂ ⊔ W).mul_mem (Subgroup.mul_mem_sup haX₂ hbW) (Subgroup.mem_sup_left (hZ hz))
  have hinf : X₂ ⊓ conjSubgroup x X₂ = Z := hA_eq
  have hsup : X₂ ⊔ conjSubgroup x X₂ = Q := le_antisymm (sup_le hXQ hWQ) hQ_le_sup
  exact ⟨x, hxM, hinf, hsup⟩

end CFSG.RankThree.GF2n.Stroth80
