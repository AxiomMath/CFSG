module

public import CFSG.Quasithin.Recognition.St84.Sec46A3
public import CFSG.Quasithin.Recognition.St84.Sec4Data
public import CFSG.Quasithin.Recognition.St84.Sec4TreeData

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

private theorem card_image_le_two_pow (X : Setup Γ G) (i : ℤ) {A : Subgroup G} (hA : A ≤ X.L i)
    (hA2 : IsPGroup 2 A) {a : V} (ha : Γ.Adj (X.vert i) a)
    (hAa : A ≤ MulAction.stabilizer G a) :
    Nat.card ↥((A.subgroupOf (X.L i)).map (X.hyp.isLocL2_oTwoPrime (X.vert i)).phi) ≤
      2 ^ X.n i := by
  classical
  set hN := X.hyp.isLocL2_oTwoPrime (X.vert i) with hNdef
  have hadj := X.hyp.adj_smul
  have hfin := X.hyp.finite_stab (X.vert i)
  have hval := X.hyp.valency (X.vert i)
  have hn : 1 ≤ X.n i := hval.1
  have hcard : Nat.card (Γ.neighborSet (X.vert i)) = 2 ^ X.n i + 1 := hval.2
  set ψ := (A.subgroupOf (X.L i)).map hN.phi with hψdef
  have hA2' : IsPGroup 2 (A.subgroupOf (X.L i)) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hA).symm
  have hψ2 : IsPGroup 2 ↥ψ := hA2'.map hN.phi
  have hψB : ψ ≤ hN.pointBorel a := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_map_of_mem hN.phi
      (Subgroup.mem_subgroupOf.mpr ⟨x.2, hAa (Subgroup.mem_subgroupOf.mp hx)⟩)
  set S : Subgroup (PSL(2, GaloisField 2 (X.n i))) :=
    (hN.pointSylow hadj hfin hcard hn a :
      Subgroup (PSL(2, GaloisField 2 (X.n i)))) with hSdef
  have hSle : S ≤ hN.pointBorel a := by
    rw [hSdef]
    exact (hN.pointSylow_spec hadj hfin hcard hn ha).1
  have hScard : Nat.card ↥S = 2 ^ X.n i := by
    rw [hSdef]
    exact psl2_sylow_two_card hn _
  have hBcard : Nat.card (hN.pointBorel a) = 2 ^ X.n i * (2 ^ X.n i - 1) :=
    hN.card_pointBorel hadj hfin hcard hn ha
  have hrel : S.relIndex (hN.pointBorel a) = 2 ^ X.n i - 1 := by
    have h := Subgroup.relIndex_mul_card (H := S) (K := hN.pointBorel a)
    rw [inf_eq_left.mpr hSle, hScard, hBcard] at h
    have hpos : 0 < 2 ^ X.n i := Nat.two_pow_pos _
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [mul_comm (2 ^ X.n i) (2 ^ X.n i - 1)] at h
    exact h
  have hSyl : IsSylowTwoOf S (hN.pointBorel a) := by
    refine ⟨hSle, ?_, ?_⟩
    · rw [hSdef]
      exact IsPGroup.of_card (psl2_sylow_two_card hn _)
    · show ¬ 2 ∣ S.relIndex (hN.pointBorel a)
      rw [hrel]
      exact (Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega))
        odd_one).not_two_dvd_nat
  have hψle : ψ ≤ S := by
    refine le_of_normal_isSylowTwoOf hSyl ?_ hψB hψ2
    rw [hN.pointBorel_eq_normalizer hadj hfin hcard hn ha]
    exact Subgroup.normal_in_normalizer
  calc Nat.card ψ ≤ Nat.card ↥S :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hψle)
          (Subgroup.inclusion_injective hψle)
    _ = 2 ^ X.n i := hScard

private theorem card_eq_card_inf_mul_card_image (X : Setup Γ G) (i : ℤ) {A : Subgroup G}
    (hA : A ≤ X.L i) :
    Nat.card ↥A = Nat.card ↥(A ⊓ X.Q i) *
      Nat.card ↥((A.subgroupOf (X.L i)).map (X.hyp.isLocL2_oTwoPrime (X.vert i)).phi) := by
  have hker : MonoidHom.ker (X.hyp.isLocL2_oTwoPrime (X.vert i)).phi =
      (X.Q i).subgroupOf (X.L i) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact (X.hyp.isLocL2_oTwoPrime (X.vert i)).phi_ker x
  rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hA, mul_comm, inf_comm]
  exact (Subgroup.relIndex_mul_card (X.Q i) A).symm

private theorem caseA_Z_one_inf_Gi (X : Setup Γ G)
    (A : X.CaseA) : X.Z 1 ⊓ X.Gi 4 = X.Z 2 ∧ X.Z 1 ⊓ X.Gi (-2) = X.Z 0 := by
  have h3 := X.caseA_3 A
  have h5d := X.caseA_5d A
  have hZ1eq : X.Z 1 = X.Z 0 ⊔ X.Z 2 := h3.2.2.2.2.2.2.1
  have hB2 : X.HasB 2 3 :=
    (X.hasB_iff_of_even (i := 2) (j := 0) (by norm_num) 3).mpr h3.1
  have hZ2G4 : X.Z 2 ≤ X.Gi 4 := hB2.Z_le_Gi (by norm_num)
  have hZ0Gm2 : X.Z 0 ≤ X.Gi (-2) := h3.1.Z_le_Gi (by norm_num)
  have hZ0infG4 : X.Z 0 ⊓ X.Gi 4 = ⊥ := by
    by_contra hne
    have hA2 : IsPGroup 2 ↥(X.Z 0 ⊓ X.Gi 4) :=
      (pCoreOf_isPGroup' (X.Gi 0)).to_le (inf_le_left.trans (X.Z_le_Q 0))
    have hfix : X.Z 0 ⊓ X.Gi 4 ≤ X.arcStab (-3) ((-3) + ((7 : ℕ) : ℤ)) := by
      rw [show (-3 : ℤ) + ((7 : ℕ) : ℤ) = 4 by norm_num,
        X.arcStab_eq_inf (show (-3 : ℤ) ≤ 4 by norm_num)]
      exact le_inf (inf_le_left.trans (h3.1.Z_le_Gi (by norm_num))) inf_le_right
    have hle := X.le_r_of_fixes A.hyp hA2 hne hfix
    omega
  have hZ2infGm2 : X.Z 2 ⊓ X.Gi (-2) = ⊥ := by
    by_contra hne
    have hA2 : IsPGroup 2 ↥(X.Z 2 ⊓ X.Gi (-2)) :=
      (pCoreOf_isPGroup' (X.Gi 2)).to_le (inf_le_left.trans (X.Z_le_Q 2))
    have hfix : X.Z 2 ⊓ X.Gi (-2) ≤ X.arcStab (-2) ((-2) + ((7 : ℕ) : ℤ)) := by
      rw [show (-2 : ℤ) + ((7 : ℕ) : ℤ) = 5 by norm_num,
        X.arcStab_eq_inf (show (-2 : ℤ) ≤ 5 by norm_num)]
      exact le_inf inf_le_right (inf_le_left.trans
        (hB2.Z_le_Gi (by norm_num)))
    have hle := X.le_r_of_fixes A.hyp hA2 hne hfix
    omega
  have hZA : X.Z 0 ⊔ X.Z 2 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [← hZ1eq, h5d.1]
    exact le_sup_right
  have hZ2N : X.Z 2 ≤ Subgroup.normalizer (X.Z 0 : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _ <| Subgroup.mem_centralizer_iff.mpr fun a ha =>
      h5d.2.2.2.1.comm (hZA (Subgroup.mem_sup_left ha)) (hZA (Subgroup.mem_sup_right hb))
  have hZ1G4 : X.Z 1 ⊓ X.Gi 4 = X.Z 2 := by
    rw [hZ1eq]
    refine le_antisymm ?_ (le_inf le_sup_right hZ2G4)
    intro x hx
    obtain ⟨hxZ, hxG⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha, b, hb, hab⟩ : x ∈ (X.Z 0 : Set G) * (X.Z 2 : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZ2N]
      exact hxZ
    change a * b = x at hab
    have hbG : b ∈ X.Gi 4 := hZ2G4 hb
    have haG : a ∈ X.Gi 4 := by
      have he : a = x * b⁻¹ := by rw [← hab]; group
      rw [he]
      exact (X.Gi 4).mul_mem hxG ((X.Gi 4).inv_mem hbG)
    have ha1 : a = 1 := by
      have hmem : a ∈ X.Z 0 ⊓ X.Gi 4 := Subgroup.mem_inf.mpr ⟨ha, haG⟩
      rw [hZ0infG4] at hmem
      simpa using hmem
    rw [← hab, ha1, one_mul]
    exact hb
  have hZ1Gm2 : X.Z 1 ⊓ X.Gi (-2) = X.Z 0 := by
    rw [hZ1eq]
    refine le_antisymm ?_ (le_inf le_sup_left hZ0Gm2)
    intro x hx
    obtain ⟨hxZ, hxG⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha, b, hb, hab⟩ : x ∈ (X.Z 0 : Set G) * (X.Z 2 : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZ2N]
      exact hxZ
    change a * b = x at hab
    have haG : a ∈ X.Gi (-2) := hZ0Gm2 ha
    have hbG : b ∈ X.Gi (-2) := by
      have he : b = a⁻¹ * x := by rw [← hab]; group
      rw [he]
      exact (X.Gi (-2)).mul_mem ((X.Gi (-2)).inv_mem haG) hxG
    have hb1 : b = 1 := by
      have hmem : b ∈ X.Z 2 ⊓ X.Gi (-2) := Subgroup.mem_inf.mpr ⟨hb, hbG⟩
      rw [hZ2infGm2] at hmem
      simpa using hmem
    rw [← hab, hb1, mul_one]
    exact ha
  exact ⟨hZ1G4, hZ1Gm2⟩

private theorem card_images_inf_le (X : Setup Γ G) :
    Nat.card ↥(((X.Q 0 ⊓ X.Q 2).subgroupOf (X.L (-1))).map
        (X.hyp.isLocL2_oTwoPrime (X.vert (-1))).phi) ≤ 2 ^ X.n 1 ∧
      Nat.card ↥((((X.Q 0 ⊓ X.Q 2) ⊓ X.Q (-1)).subgroupOf (X.L 3)).map
        (X.hyp.isLocL2_oTwoPrime (X.vert 3)).phi) ≤ 2 ^ X.n 1 := by
  classical
  have hQ0m1 : X.Q 0 ≤ X.Gi (-1) := by
    intro q hq
    have h := (X.Q_le_Gi_adj 0) hq
    rw [show (0 : ℤ) - 1 = -1 by norm_num] at h
    exact h.1
  have hQ23 : X.Q 2 ≤ X.Gi 3 := by
    intro q hq
    have h := (X.Q_le_Gi_adj 2) hq
    rw [show (2 : ℤ) + 1 = 3 by norm_num] at h
    exact h.2
  have hA1_2 : IsPGroup 2 ↥(X.Q 0 ⊓ X.Q 2) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left
  have hA1Lm1 : X.Q 0 ⊓ X.Q 2 ≤ X.L (-1) :=
    le_oTwoPrime_of_isPGroup hA1_2 (inf_le_left.trans hQ0m1)
  have hadj_m1 : Γ.Adj (X.vert (-1)) (X.vert 0) := by
    have h := X.adj (-1)
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  have hA1fix0 : X.Q 0 ⊓ X.Q 2 ≤ MulAction.stabilizer G (X.vert 0) :=
    inf_le_left.trans (X.Q_le_Gi 0)
  have himg1 : Nat.card ↥(((X.Q 0 ⊓ X.Q 2).subgroupOf (X.L (-1))).map
      (X.hyp.isLocL2_oTwoPrime (X.vert (-1))).phi) ≤ 2 ^ X.n (-1) :=
    X.card_image_le_two_pow (-1) hA1Lm1 hA1_2 hadj_m1 hA1fix0
  have hn1 : X.n (-1) = X.n 1 := by
    simpa using (X.n_add 1 (-1)).symm
  rw [hn1] at himg1
  have hA'2 : IsPGroup 2 ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1)) :=
    hA1_2.to_le (show X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ≤ X.Q 0 ⊓ X.Q 2 from inf_le_left)
  have hA'L3 : X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ≤ X.L 3 :=
    le_oTwoPrime_of_isPGroup hA'2 (inf_le_left.trans (inf_le_right.trans hQ23))
  have hadj_3 : Γ.Adj (X.vert 3) (X.vert 2) := by
    have h := (X.adj 2).symm
    rwa [show (2 : ℤ) + 1 = 3 by norm_num] at h
  have hA'fix2 : X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ≤ MulAction.stabilizer G (X.vert 2) :=
    (inf_le_left.trans inf_le_right).trans (X.Q_le_Gi 2)
  have himg2 : Nat.card ↥((((X.Q 0 ⊓ X.Q 2) ⊓ X.Q (-1)).subgroupOf (X.L 3)).map
      (X.hyp.isLocL2_oTwoPrime (X.vert 3)).phi) ≤ 2 ^ X.n 3 :=
    X.card_image_le_two_pow 3 hA'L3 hA'2 hadj_3 hA'fix2
  have hn3 : X.n 3 = X.n 1 := by
    simpa using X.n_add 1 1
  rw [hn3] at himg2
  exact ⟨himg1, himg2⟩

private theorem caseA_two_pow_le_card_inf (X : Setup Γ G)
    (A : X.CaseA) : 2 ^ X.n 0 ≤ Nat.card ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ⊓ X.Q 3) := by
  have hA1card := caseA_card_Q_zero_inf_Q_two X A
  obtain ⟨himg1, himg2⟩ := card_images_inf_le X
  have hA1_2 : IsPGroup 2 ↥(X.Q 0 ⊓ X.Q 2) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left
  have hA1Lm1 : X.Q 0 ⊓ X.Q 2 ≤ X.L (-1) := by
    refine le_oTwoPrime_of_isPGroup hA1_2 ?_
    intro q hq
    have h := (X.Q_le_Gi_adj 0) hq.1
    rw [show (0 : ℤ) - 1 = -1 by norm_num] at h
    exact h.1
  have hA1G3 : X.Q 0 ⊓ X.Q 2 ≤ X.Gi 3 := by
    intro q hq
    have h := (X.Q_le_Gi_adj 2) hq.2
    rw [show (2 : ℤ) + 1 = 3 by norm_num] at h
    exact h.2
  have hA'2 : IsPGroup 2 ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1)) :=
    hA1_2.to_le (show X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ≤ X.Q 0 ⊓ X.Q 2 from inf_le_left)
  have hA'L3 : X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ≤ X.L 3 :=
    le_oTwoPrime_of_isPGroup hA'2 (inf_le_left.trans hA1G3)
  have hcard1 : Nat.card ↥(X.Q 0 ⊓ X.Q 2) =
      Nat.card ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1)) *
        Nat.card ↥(((X.Q 0 ⊓ X.Q 2).subgroupOf (X.L (-1))).map
          (X.hyp.isLocL2_oTwoPrime (X.vert (-1))).phi) :=
    X.card_eq_card_inf_mul_card_image (-1) hA1Lm1
  have hcard2 : Nat.card ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1)) =
      Nat.card ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ⊓ X.Q 3) *
        Nat.card ↥((((X.Q 0 ⊓ X.Q 2) ⊓ X.Q (-1)).subgroupOf (X.L 3)).map
          (X.hyp.isLocL2_oTwoPrime (X.vert 3)).phi) :=
    X.card_eq_card_inf_mul_card_image 3 hA'L3
  have hle0 : Nat.card ↥(X.Q 0 ⊓ X.Q 2) ≤
      Nat.card ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ⊓ X.Q 3) * 2 ^ (2 * X.n 1) := by
    rw [hcard1, hcard2]
    calc (Nat.card ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ⊓ X.Q 3) *
          Nat.card ↥((((X.Q 0 ⊓ X.Q 2) ⊓ X.Q (-1)).subgroupOf (X.L 3)).map
            (X.hyp.isLocL2_oTwoPrime (X.vert 3)).phi)) *
          Nat.card ↥(((X.Q 0 ⊓ X.Q 2).subgroupOf (X.L (-1))).map
            (X.hyp.isLocL2_oTwoPrime (X.vert (-1))).phi)
        ≤ (Nat.card ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ⊓ X.Q 3) * 2 ^ X.n 1) * 2 ^ X.n 1 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ himg2) himg1
      _ = Nat.card ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ⊓ X.Q 3) * 2 ^ (2 * X.n 1) := by
          rw [mul_assoc, ← pow_add]
          congr 2
          ring
  rw [hA1card] at hle0
  have hmain : 2 ^ X.n 0 * 2 ^ (2 * X.n 1) ≤
      Nat.card ↥(X.Q 0 ⊓ X.Q 2 ⊓ X.Q (-1) ⊓ X.Q 3) * 2 ^ (2 * X.n 1) := by
    rwa [← pow_add]
  exact Nat.le_of_mul_le_mul_right hmain (Nat.two_pow_pos _)

private theorem caseA_pCoreOf_arcStab_ne_bot
    (X : Setup Γ G) (A : X.CaseA) : pCoreOf 2 (X.arcStab (-2) 4) ≠ ⊥ := by
  have h5b := X.caseA_5b A
  have hU'card := X.caseA_two_pow_le_card_inf A
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2 with hA1def
  have hU'ne : A1 ⊓ X.Q (-1) ⊓ X.Q 3 ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hU'card
    have h4 : 4 ≤ 2 ^ X.n 0 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ X.n 0 := pow_le_pow_right' (by norm_num) (A.hyp.two_le_n 0)
    omega
  have hU'2 : IsPGroup 2 ↥(A1 ⊓ X.Q (-1) ⊓ X.Q 3) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hU'fix : A1 ⊓ X.Q (-1) ⊓ X.Q 3 ≤ X.arcStab (-2) 4 := by
    rw [X.arcStab_eq_inf (show (-2 : ℤ) ≤ 4 by norm_num)]
    refine le_inf ?_ ?_
    · exact (inf_le_left.trans inf_le_right).trans ((X.Q_le_Gi_adj (-1)).trans inf_le_left)
    · exact inf_le_right.trans ((X.Q_le_Gi_adj 3).trans inf_le_right)
  intro hbot
  have hle : A1 ⊓ X.Q (-1) ⊓ X.Q 3 ≤ pCoreOf 2 (X.arcStab (-2) 4) :=
    X.le_pCoreOf_arcStab_r A.hyp hU'2 hU'fix
  rw [hbot] at hle
  exact hU'ne (le_bot_iff.mp hle)

theorem caseA_5e (X : Setup Γ G) (A : X.CaseA) :
    (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) =
        pCoreOf 2 (X.arcStab (-2) 4) ∧
      X.LeftTransAt (-2) 4 ∧ X.RightTransAt (-2) 4 := by
  classical
  have h3 := X.caseA_3 A
  have h5d := X.caseA_5d A
  set D : Subgroup G := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hDdef
  set P : Subgroup G := pCoreOf 2 (X.arcStab (-2) 4) with hPdef
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2 with hA1def
  have hPle : P ≤ X.arcStab (-2) 4 := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hPG : ∀ k : ℤ, -2 ≤ k → k ≤ 4 → P ≤ X.Gi k := fun k h1 h2 =>
    hPle.trans (X.arcStab_le_Gi_of_between h1 h2)
  have hPleQ0 : P ≤ X.Q 0 :=
    X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by norm_num) (by norm_num)
  have hPleQ2 : P ≤ X.Q 2 :=
    X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by norm_num) (by norm_num)
  have hPleA1 : P ≤ A1 := by rw [hA1def]; exact le_inf hPleQ0 hPleQ2
  have hPleQ1 : P ≤ X.Q 1 :=
    X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by norm_num) (by norm_num)
  have hZ0Z2 : X.Z 0 ⊓ X.Z 2 = ⊥ := h3.2.2.2.2.2.2.2
  obtain ⟨hZ1G4, hZ1Gm2⟩ := X.caseA_Z_one_inf_Gi A
  have hPinfZ1 : P ⊓ X.Z 1 = ⊥ := by
    refine le_bot_iff.mp ?_
    calc P ⊓ X.Z 1 ≤ (X.Z 1 ⊓ X.Gi 4) ⊓ (X.Z 1 ⊓ X.Gi (-2)) :=
          le_inf (le_inf inf_le_right (inf_le_left.trans (hPG 4 (by norm_num) (by norm_num))))
            (le_inf inf_le_right (inf_le_left.trans (hPG (-2) (by norm_num) (by norm_num))))
      _ = ⊥ := by rw [hZ1G4, hZ1Gm2, inf_comm, hZ0Z2]
  have hKinvP : X.K ≤ Subgroup.normalizer (P : Set G) :=
    (X.K_le_GT.trans (X.GT_le_arcStab (-2) 4)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hKiL1 : X.Ki 1 ≤ X.L 1 := by rw [Setup.Ki]; exact inf_le_right
  have hcommP : ⁅P, X.Ki 1⁆ ≤ X.Z 1 :=
    (Subgroup.commutator_mono hPleA1 hKiL1).trans h5d.2.2.2.2.1
  have hKiN : X.Ki 1 ≤ Subgroup.normalizer (P : Set G) := fun k hk =>
    hKinvP (Subgroup.mem_inf.mp hk).1
  have hcommP' : ⁅P, X.Ki 1⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hKiN
  have hPleC : P ≤ Subgroup.centralizer (X.Ki 1 : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hle : ⁅P, X.Ki 1⁆ ≤ P ⊓ X.Z 1 := le_inf hcommP' hcommP
    rw [hPinfZ1] at hle
    exact le_bot_iff.mp hle
  have hPleD : P ≤ D := by rw [hDdef]; exact le_inf hPleQ1 hPleC
  have hDcard : Nat.card ↥D = 2 ^ X.n 0 := h5d.2.2.1
  have hPne : P ≠ ⊥ := X.caseA_pCoreOf_arcStab_ne_bot A
  have hPcard : Nat.card ↥P = 2 ^ X.n 0 := by
    have h : Nat.card ↥P = 2 ^ X.n (-2) := by
      rw [hPdef]
      exact (X.pCoreOf_arcStab_r A.hyp (-2) hPne).1
    rwa [show (-2 : ℤ) = 0 + 2 * (-1) by norm_num, X.n_add (-1) 0] at h
  have hDGi : D ≤ X.Gi 1 := by
    rw [hDdef]; exact inf_le_left.trans (X.Q_le_Gi 1)
  haveI : Finite ↥D := finite_of_le_stabilizer X.hyp (H := D) hDGi
  have hDP : D = P := (Subgroup.eq_of_le_of_card_ge hPleD (by rw [hPcard, hDcard])).symm
  have htrans := X.pCoreOf_arcStab_r A.hyp (-2) hPne
  exact ⟨hDP, htrans.2.2.2.1, htrans.2.2.2.2⟩

private theorem caseA_exists_Qg_six_smul
    (X : Setup Γ G) (A : X.CaseA) :
    ∀ x : V, Γ.Adj (X.vert 0) x → x ≠ X.vert 1 → ∃ q ∈ X.Qg 6, q • X.vert (-1) = x := by
  have h5d := X.caseA_5d A
  have h5e := X.caseA_5e A
  set D := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hDdef
  have hDcard : Nat.card ↥D = 2 ^ X.n 0 := h5d.2.2.1
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    exact (Nat.one_lt_two_pow (by have := A.hyp.two_le_n 0; omega)).ne' hDcard.symm
  have hQeq : X.Qg 6 = conjSub X.τ D := by
    have h6 : X.arcStab 0 ((6 : ℕ) : ℤ) = conjSub X.τ (X.arcStab (-2) 4) := by
      have h := X.arcStab_add 1 (-2) 4
      norm_num at h ⊢
      exact h
    rw [Setup.Qg, h6, pCoreOf_conjSub, ← h5e.1]
  have hQne : X.Qg 6 ≠ ⊥ := by
    rw [hQeq]
    intro h
    rw [conjSub_eq_bot_iff] at h
    exact hDne h
  intro x hx hx1
  have hKA : X.K ≤ X.arcStab 0 6 := X.K_le_GT.trans (X.GT_le_arcStab 0 6)
  have hA : X.arcStab 0 6 ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf (X.arcStab_le_Gi_left (by norm_num))
      (X.arcStab_le_Gi_left_succ (by norm_num))
  obtain ⟨-, hKsup⟩ := X.pCoreOf_eq_inf_edgeSylow 0 hKA hA
  have hleft := (X.pCoreOf_arcStab_r A.hyp 0 hQne).2.2.2.1
  have hadj : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    have h := (X.adj (-1)).symm
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  have hne : X.vert (-1) ≠ X.vert 1 := by
    intro h
    have hv := X.vert_injective h
    norm_num at hv
  obtain ⟨g, hg, hgx⟩ := hleft (X.vert (-1)) x hadj hne hx hx1
  have hKN : X.K ≤ Subgroup.normalizer ((X.Qg 6) : Set G) :=
    hKA.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hcoe : (↑(X.K ⊔ X.Qg 6) : Set G) = (X.K : Set G) * (X.Qg 6 : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X.K (X.Qg 6) hKN
  have hKsup' : X.K ⊔ X.Qg 6 = X.arcStab 0 6 := hKsup
  have hgm : g ∈ (X.K : Set G) * (X.Qg 6 : Set G) := by
    rw [← hcoe, hKsup']
    exact hg
  obtain ⟨k, hkK, q, hqQ, hkq⟩ := hgm
  refine ⟨k * q * k⁻¹, ?_, ?_⟩
  · simpa using (Subgroup.mem_normalizer_iff''.mp (hKN (X.K.inv_mem hkK)) q).mp hqQ
  · have hgx' : (k * q) • X.vert (-1) = x := by
      have h : (k * q) = g := hkq
      rw [h]
      exact hgx
    calc (k * q * k⁻¹) • X.vert (-1) = k • (q • (k⁻¹ • X.vert (-1))) := by
            rw [mul_smul, mul_smul]
      _ = k • (q • X.vert (-1)) := by rw [X.K_fix k⁻¹ (X.K.inv_mem hkK) (-1)]
      _ = (k * q) • X.vert (-1) := by rw [← mul_smul]
      _ = x := hgx'
private theorem caseA_iSup_conj_Z_one_le_centralizer
    (X : Setup Γ G) (A : X.CaseA) {D : Subgroup G} (hDQ : D ≤ X.Q 1)
    (hDQm1 : D ≤ X.Q (-1)) (hDcent : D ≤ Subgroup.centralizer (X.Q 1 : Set G)) :
    (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ≤ Subgroup.centralizer (D : Set G) := by
  have hQtr := X.caseA_exists_Qg_six_smul A
  refine iSup_le fun h => iSup_le fun hh => ?_
  by_cases hfix : h • X.vert 1 = X.vert 1
  · have hhG1 : h ∈ X.Gi 1 := MulAction.mem_stabilizer_iff.mpr hfix
    rw [X.Z_normal 1 h hhG1, Subgroup.le_centralizer_iff]
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc : z ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2
    exact (Subgroup.mem_centralizer_iff.mp hzc d (hDQ hd)).symm
  · have hadj : Γ.Adj (X.vert 0) (h • X.vert 1) := by
      have h1 : h ∈ X.Gi 0 := hh
      have hadj0 : Γ.Adj (X.vert 0) (X.vert 1) := by simpa using X.adj 0
      have h2 := (X.hyp.adj_smul h (X.vert 0) (X.vert 1)).2 hadj0
      rwa [MulAction.mem_stabilizer_iff.mp hh] at h2
    obtain ⟨q, hqQ, hqx⟩ := hQtr (h • X.vert 1) hadj hfix
    have hqQ1 : q ∈ X.Q 1 := by
      have hqArc : q ∈ X.arcStab 0 6 := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hqQ
      have hqG1 : q ∈ X.Gi 1 :=
        X.arcStab_le_Gi_of_between (by norm_num) (by norm_num) hqArc
      have hq2 : q ^ 2 = 1 := (X.isElemAbelian_pCoreOf_arcStab_r A.hyp 0).2 q hqQ
      have ha2 : Γ.Adj (X.vert 1) (X.vert 0) := by
        have h := (X.adj 0).symm
        rwa [show (0 : ℤ) + 1 = 1 by norm_num] at h
      have hb2 : Γ.Adj (X.vert 1) (X.vert 2) := by
        have h := X.adj 1
        rwa [show (1 : ℤ) + 1 = 2 by norm_num] at h
      refine mem_pCoreOf_of_fixes_two X.hyp hqG1 ⟨1, by simpa using hq2⟩
        (a := X.vert 0) (b := X.vert 2) ha2 hb2 ?_ ?_ ?_
      · intro h
        have hv := X.vert_injective h
        norm_num at hv
      · exact MulAction.mem_stabilizer_iff.mp
          (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num) hqArc)
      · exact MulAction.mem_stabilizer_iff.mp
          (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num) hqArc)
    have htrans : conjSub (q⁻¹ * h) (X.Z 1) = X.Z (-1) :=
      (X.Z_smul X (by rw [mul_smul, ← hqx, inv_smul_smul] :
        (q⁻¹ * h) • X.vert 1 = X.vert (-1))).symm
    have hconj : conjSub h (X.Z 1) = conjSub q (X.Z (-1)) := by
      rw [show h = q * (q⁻¹ * h) by group, conjSub_mul, htrans]
    rw [hconj, Subgroup.le_centralizer_iff]
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
    have hqd : d * q = q * d :=
      (Subgroup.mem_centralizer_iff.mp (hDcent hd) q hqQ1).symm
    have hdz : d * z₀ = z₀ * d :=
      Subgroup.mem_centralizer_iff.mp
        ((Subgroup.mem_inf.mp (X.Z_le_center (-1) hz₀)).2) d (hDQm1 hd)
    have hcomm : Commute d q := hqd
    have hqi : d * q⁻¹ = q⁻¹ * d := hcomm.inv_right
    change q * z₀ * q⁻¹ * d = d * (q * z₀ * q⁻¹)
    calc q * z₀ * q⁻¹ * d = q * z₀ * (q⁻¹ * d) := by group
      _ = q * z₀ * (d * q⁻¹) := by rw [← hqi]
      _ = q * (z₀ * d) * q⁻¹ := by group
      _ = q * (d * z₀) * q⁻¹ := by rw [← hdz]
      _ = (q * d) * z₀ * q⁻¹ := by group
      _ = (d * q) * z₀ * q⁻¹ := by rw [← hqd]
      _ = d * (q * z₀ * q⁻¹) := by group

private theorem caseA_commutator_D_Q_one_ne_bot
    (X : Setup Γ G) (A : X.CaseA) :
    ⁅X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G), X.Q 1⁆ ≠ ⊥ := by
  have h5d := X.caseA_5d A
  have h5e := X.caseA_5e A
  have hAcomm : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2) := h5d.2.2.2.1
  set D := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hDdef
  have hDQ : D ≤ X.Q 1 := inf_le_left
  have hDA : D ≤ X.Q 0 ⊓ X.Q 2 := h5d.1.symm ▸ le_sup_left
  have hDQ0 : D ≤ X.Q 0 := hDA.trans inf_le_left
  have hDcard : Nat.card ↥D = 2 ^ X.n 0 := h5d.2.2.1
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    exact (Nat.one_lt_two_pow (by have := A.hyp.two_le_n 0; omega)).ne' hDcard.symm
  have hDArc : D ≤ X.arcStab (-2) 4 := by
    rw [h5e.1]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hDGi : ∀ k : ℤ, -2 ≤ k → k ≤ 4 → D ≤ X.Gi k := fun k h1 h2 =>
    hDArc.trans (X.arcStab_le_Gi_of_between h1 h2)
  have hDQm1 : D ≤ X.Q (-1) := by
    rw [h5e.1]
    exact X.pCoreOf_arcStab_le_Q_of_lt_of_lt (by norm_num) (by norm_num)
  intro hbot
  have hDcent : D ≤ Subgroup.centralizer (X.Q 1 : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have hDVle := X.caseA_iSup_conj_Z_one_le_centralizer A hDQ hDQm1 hDcent
  have hQ0leC : X.Q 0 ≤ Subgroup.centralizer (D : Set G) := by
    rw [h5d.2.2.2.2.2]
    exact sup_le hDVle fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hAcomm.comm (hDA hy) (hDA hx)
  have hDcentQ0 : D ≤ Subgroup.centralizer (X.Q 0 : Set G) :=
    Subgroup.le_centralizer_iff.mpr hQ0leC
  have hDZQ0 : D ≤ centerOf (X.Q 0) := le_inf hDQ0 hDcentQ0
  obtain ⟨t, ht, htref⟩ := X.exists_reflection A.hyp 1
  have ht0 : t • X.vert 0 = X.vert 2 := by
    have h := htref (-1)
    rwa [show (1 : ℤ) + (-1) = 0 by norm_num, show (1 : ℤ) - (-1) = 2 by norm_num] at h
  have hDconj : conjSub t D = D := by
    rw [h5e.1, ← pCoreOf_conjSub]
    congr 1
    unfold Setup.arcStab
    rw [conjSub_fixSet]
    congr 1
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := hv
      obtain ⟨k, hk, rfl⟩ := hw
      rw [Set.mem_Icc] at hk
      refine ⟨2 - k, ⟨by omega, by omega⟩, ?_⟩
      have h := htref (k - 1)
      rw [show (1 : ℤ) + (k - 1) = k by ring,
        show (1 : ℤ) - (k - 1) = 2 - k by ring] at h
      exact h.symm
    · intro hv
      obtain ⟨k, hk, rfl⟩ := hv
      rw [Set.mem_Icc] at hk
      refine ⟨X.vert (2 - k), ⟨2 - k, ⟨by omega, by omega⟩, rfl⟩, ?_⟩
      have h := htref (1 - k)
      rw [show (1 : ℤ) + (1 - k) = 2 - k by ring,
        show (1 : ℤ) - (1 - k) = k by ring] at h
      exact h
  have hQ2 : X.Q 2 = conjSub t (X.Q 0) := X.Q_smul X ht0
  have hDZQ2 : D ≤ centerOf (X.Q 2) := by
    have hZc : conjSub t (centerOf (X.Q 0)) = centerOf (X.Q 2) := by
      rw [hQ2, centerOf_conjSub]
    rw [← hZc, ← hDconj]
    exact conjSub_mono t hDZQ0
  have hedge0 : X.edgeSylow 0 ≤ Subgroup.centralizer (D : Set G) := by
    rw [← X.sup_Q_eq_edgeSylow A.hyp.char 0, show (0 : ℤ) + 1 = 1 by norm_num]
    exact sup_le (Subgroup.le_centralizer_iff.mpr hDcentQ0)
      (Subgroup.le_centralizer_iff.mpr hDcent)
  have hedge1 : X.edgeSylow 1 ≤ Subgroup.centralizer (D : Set G) := by
    rw [← X.sup_Q_eq_edgeSylow A.hyp.char 1, show (1 : ℤ) + 1 = 2 by norm_num]
    exact sup_le (Subgroup.le_centralizer_iff.mpr hDcent)
      (Subgroup.le_centralizer_iff.mpr fun d hd => (hDZQ2 hd).2)
  have hDGi1 : D ≤ X.Gi 1 := hDGi 1 (by norm_num) (by norm_num)
  have hDL1 : D ≤ centerOf (X.L 1) :=
    X.le_centerOf_L A.hyp.char 1 hDGi1 hedge0 hedge1
  rw [(X.caseA_3 A).2.2.2.2.1] at hDL1
  exact hDne (le_bot_iff.mp hDL1)

private theorem L_one_le_normalizer_commutator (X : Setup Γ G) {D : Subgroup G}
    (hDL : ⁅D, X.L 1⁆ ≤ X.Z 1) (hDZ1 : ⁅D, X.Q 1⁆ ≤ X.Z 1) :
    X.L 1 ≤ Subgroup.normalizer (⁅D, X.Q 1⁆ : Subgroup G) := by
  have hle : ∀ g ∈ X.L 1, conjSub g ⁅D, X.Q 1⁆ ≤ ⁅D, X.Q 1⁆ := by
    intro g hg
    have hQ : conjSub g (X.Q 1) = X.Q 1 :=
      mem_normalizer_iff_conjSub.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) (X.L_le_Gi 1 hg))
    rw [← conjSub_commutator, hQ, Subgroup.commutator_le]
    intro a ha x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp ha
    have hdl : ⁅g, d⁆ ∈ X.Z 1 := by
      have h : ⁅d, g⁆ ∈ X.Z 1 :=
        (Subgroup.commutator_le.mp hDL) d hd g hg
      rw [show ⁅g, d⁆ = ⁅d, g⁆⁻¹ from (commutatorElement_inv d g).symm]
      exact (X.Z 1).inv_mem h
    have hzQ : ⁅g, d⁆ ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 1 hdl)).2
    have hdxZ : ⁅d, x⁆ ∈ X.Z 1 := hDZ1 (Subgroup.commutator_mem_commutator hd hx)
    have hcommz : ⁅⁅g, d⁆, x⁆ = 1 := by
      have hz1 : ⁅g, d⁆ * x = x * ⁅g, d⁆ :=
        ((Subgroup.mem_centralizer_iff.mp hzQ) x hx).symm
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact hz1
    have he : ⁅(MulAut.conj g) d, x⁆ = ⁅d, x⁆ := by
      have hconj : (MulAut.conj g) d = ⁅g, d⁆ * d := conj_eq_commutatorElement_mul
      have hcomm : ⁅g, d⁆ * ⁅d, x⁆ = ⁅d, x⁆ * ⁅g, d⁆ :=
        X.Z_commute 1 ⁅g, d⁆ hdl ⁅d, x⁆ hdxZ
      calc ⁅(MulAut.conj g) d, x⁆ = ⁅⁅g, d⁆ * d, x⁆ := by rw [hconj]
        _ = ⁅g, d⁆ * ⁅d, x⁆ * ⁅g, d⁆⁻¹ * ⁅⁅g, d⁆, x⁆ :=
            commutatorElement_mul_left_eq_conj_mul _ _ _
        _ = ⁅g, d⁆ * ⁅d, x⁆ * ⁅g, d⁆⁻¹ := by rw [hcommz, mul_one]
        _ = ⁅d, x⁆ * ⁅g, d⁆ * ⁅g, d⁆⁻¹ := by rw [hcomm]
        _ = ⁅d, x⁆ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    change ⁅(MulAut.conj g) d, x⁆ ∈ ⁅D, X.Q 1⁆
    rw [he]
    exact Subgroup.commutator_mem_commutator hd hx
  intro l hl
  rw [mem_normalizer_iff_conjSub]
  refine le_antisymm (hle l hl) ?_
  have h1 := conjSub_mono l (hle l⁻¹ ((X.L 1).inv_mem hl))
  rwa [conjSub_inv_conjSub] at h1

theorem caseA_5f (X : Setup Γ G) (A : X.CaseA) :
    ⁅X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G), X.Q 1⁆ = X.Z 1 ∧
      (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊓
        Subgroup.centralizer (X.Q 1 : Set G) = ⊥ := by
  have h5d := X.caseA_5d A
  have h5e := X.caseA_5e A
  have h3 := X.caseA_3 A
  have hnatZ : NatQuot (X.L 1) (X.Z 1) ⊥ (X.n 1) := h3.2.2.2.2.2.1
  set D := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hDdef
  have hDA : D ≤ X.Q 0 ⊓ X.Q 2 := h5d.1.symm ▸ le_sup_left
  have hQ1L1 : X.Q 1 ≤ X.L 1 := X.Q_le_L 1
  have hDZ1 : ⁅D, X.Q 1⁆ ≤ X.Z 1 :=
    (Subgroup.commutator_mono hDA hQ1L1).trans h5d.2.2.2.2.1
  have hne : ⁅D, X.Q 1⁆ ≠ ⊥ := X.caseA_commutator_D_Q_one_ne_bot A
  have hinv : X.L 1 ≤ Subgroup.normalizer (⁅D, X.Q 1⁆ : Subgroup G) :=
    X.L_one_le_normalizer_commutator
      ((Subgroup.commutator_mono hDA le_rfl).trans h5d.2.2.2.2.1) hDZ1
  have hcommmid : ⁅D, X.Q 1⁆ = X.Z 1 := by
    rcases hnatZ.irred ⁅D, X.Q 1⁆ bot_le hDZ1 hinv with h | h
    · exact absurd h hne
    · exact h
  refine ⟨hcommmid, ?_⟩
  set U := D ⊓ Subgroup.centralizer (X.Q 1 : Set G) with hUdef
  have hUP : U ≤ pCoreOf 2 (X.arcStab (-2) ((-2) + ((6 : ℕ) : ℤ))) := by
    rw [show (-2 : ℤ) + ((6 : ℕ) : ℤ) = 4 by norm_num, ← h5e.1]
    exact inf_le_left
  have hUneqD : U ≠ D := by
    intro hUD
    have hDle : D ≤ Subgroup.centralizer (X.Q 1 : Set G) := hUD ▸ inf_le_right
    have hbot : ⁅D, X.Q 1⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDle
    rw [hcommmid] at hbot
    have hc4 : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 1) := by
      rw [← Subgroup.relIndex_bot_left (H := X.Z 1), hnatZ.index]
    rw [hbot, Subgroup.card_bot] at hc4
    exact (Nat.one_lt_two_pow (by have := A.hyp.two_le_n 1; omega)).ne' hc4.symm
  have hKinv : X.K ≤ Subgroup.normalizer (U : Set G) := by
    intro k hk
    have hkG1 : k ∈ X.Gi 1 := X.K_le_Gi 1 hk
    have hQ1 : conjSub k (X.Q 1) = X.Q 1 :=
      mem_normalizer_iff_conjSub.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) hkG1)
    have hDconj : conjSub k D = D :=
      mem_normalizer_iff_conjSub.mp (X.K_le_normalizer_Q_inf_centralizer_Ki 1 hk)
    rw [mem_normalizer_iff_conjSub]
    rw [hUdef]
    change conjSub k (D ⊓ Subgroup.centralizer (X.Q 1 : Set G)) = _
    rw [conjSub_inf, hDconj, ← conjSub_centralizer, hQ1]
  by_cases hUbot : U = ⊥
  · exact hUbot
  · exfalso
    have heq := X.eq_of_le_pCoreOf_arcStab_r A.hyp hKinv hUbot hUP
    rw [show (-2 : ℤ) + ((6 : ℕ) : ℤ) = 4 by norm_num, ← h5e.1] at heq
    exact hUneqD heq

private theorem isElemSec_Q_zero_of_eq_sup (X : Setup Γ G) (V D : Subgroup G)
    (hQ0eq : X.Q 0 = V ⊔ D) (hVQ0 : ⁅V, X.Q 0⁆ ≤ X.Z 0) (hVsq : ∀ x ∈ V, x ^ 2 ∈ X.Z 0)
    (hDelem : IsElemAbelian 2 D) (hDN : D ≤ Subgroup.normalizer (V : Set G)) :
    IsElemSec (X.Z 0) (X.Q 0) := by
  have hVleQ0 : V ≤ X.Q 0 := hQ0eq ▸ le_sup_left
  have hDleQ0 : D ≤ X.Q 0 := hQ0eq ▸ le_sup_right
  have hprod : (X.Q 0 : Set G) = (V : Set G) * (D : Set G) := by
    rw [hQ0eq, Subgroup.coe_mul_of_right_le_normalizer_left V D hDN]
  have hDV : ⁅D, V⁆ ≤ X.Z 0 := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hDleQ0).trans hVQ0
  have hcommQ0 : ⁅X.Q 0, X.Q 0⁆ ≤ X.Z 0 := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨v₁, hv₁, d₁, hd₁, rfl⟩ : x ∈ (V : Set G) * (D : Set G) := by
      rw [← hprod]; exact hx
    obtain ⟨v₂, hv₂, d₂, hd₂, rfl⟩ : y ∈ (V : Set G) * (D : Set G) := by
      rw [← hprod]; exact hy
    have hdd : ⁅d₁, d₂⁆ = 1 := by
      refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
      exact hDelem.comm hd₁ hd₂
    have hd1y : ⁅d₁, v₂ * d₂⁆ ∈ X.Z 0 := by
      rw [commutatorElement_mul_right_eq_mul_conj, hdd, mul_one, mul_assoc,
        mul_inv_cancel, mul_one]
      exact hDV (Subgroup.commutator_mem_commutator hd₁ hv₂)
    have hcomm1 : ⁅v₁, v₂ * d₂⁆ ∈ X.Z 0 :=
      hVQ0 (Subgroup.commutator_mem_commutator hv₁ (hQ0eq ▸ Subgroup.mul_mem_sup hv₂ hd₂))
    have hcz : v₁ * ⁅d₁, v₂ * d₂⁆ * v₁⁻¹ ∈ X.Z 0 := by
      have hzc : v₁ * ⁅d₁, v₂ * d₂⁆ = ⁅d₁, v₂ * d₂⁆ * v₁ :=
        Subgroup.mem_centralizer_iff.mp
          (Subgroup.mem_inf.mp (X.Z_le_center 0 hd1y)).2 v₁ (hVleQ0 hv₁)
      rw [hzc, mul_assoc, mul_inv_cancel, mul_one]
      exact hd1y
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact (X.Z 0).mul_mem hcz hcomm1
  have hsqQ0 : ∀ x ∈ X.Q 0, x ^ 2 ∈ X.Z 0 := by
    have hmemQ : ∀ y : G, y ∈ Subgroup.closure ((V : Set G) ∪ (D : Set G)) → y ∈ X.Q 0 := by
      intro y hy
      rw [← Subgroup.sup_eq_closure] at hy
      exact hQ0eq ▸ hy
    intro x hx
    rw [hQ0eq, Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with hy | hy
        · exact hVsq y hy
        · have hy2 : y ^ 2 = 1 := hDelem.2 y hy
          rw [hy2]
          exact (X.Z 0).one_mem
    | one =>
        rw [one_pow]
        exact (X.Z 0).one_mem
    | mul a b ha hb iha ihb =>
        have haQ : a ∈ X.Q 0 := hmemQ a ha
        have hbQ : b ∈ X.Q 0 := hmemQ b hb
        have hcomm_ab : ⁅a, b⁆ ∈ X.Z 0 :=
          hcommQ0 (Subgroup.commutator_mem_commutator haQ hbQ)
        have hbaZ : ⁅b, a⁆ ∈ X.Z 0 := by
          rw [← commutatorElement_inv]
          exact (X.Z 0).inv_mem hcomm_ab
        have hcommz : a * ⁅b, a⁆ = ⁅b, a⁆ * a :=
          Subgroup.mem_centralizer_iff.mp
            (Subgroup.mem_inf.mp (X.Z_le_center 0 hbaZ)).2 a haQ
        have he : (a * b) ^ 2 = a ^ 2 * ⁅b, a⁆ * b ^ 2 := by
          have hba : b * a = ⁅b, a⁆ * a * b := by
            rw [commutatorElement_def]; group
          rw [pow_two, pow_two, pow_two]
          calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (⁅b, a⁆ * a * b) * b := by rw [hba]
            _ = a * (a * ⁅b, a⁆ * b) * b := by rw [hcommz]
            _ = (a * a) * ⁅b, a⁆ * (b * b) := by group
        rw [he]
        exact (X.Z 0).mul_mem ((X.Z 0).mul_mem iha hbaZ) ihb
    | inv y hy ihy =>
        rw [inv_pow]
        exact (X.Z 0).inv_mem ihy
  exact ⟨X.Z_le_Q 0, hcommQ0, hsqQ0⟩

private theorem isSpecialPGroup_of_centerOf_eq {P Z : Subgroup G} [Finite ↥P]
    (hP : IsPGroup 2 ↥P) (hZelem : IsElemAbelian 2 Z) (hcenter : centerOf P = Z)
    (hsq : ∀ x ∈ P, x ^ 2 ∈ Z) (hcomm : ⁅P, P⁆ = Z) : IsSpecialPGroup 2 ↥P := by
  have hmapc := CFSG.Quasithin.F6.map_center_eq_centerOf P
  have hcommimg : (commutator ↥P).map P.subtype = Z := by
    rw [Subgroup.map_subtype_commutator, hcomm]
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hP⟩
  have hfr : frattini ↥P =
      Subgroup.closure (((commutator ↥P : Subgroup ↥P) : Set ↥P) ∪
        Set.range (fun x : ↥P => x ^ 2)) :=
    CFSG.frattini_eq_closure_commutator_union_powers (R := ↥P) (p := 2)
  refine ⟨hP, Or.inr ⟨?_, ?_, ?_⟩⟩
  · apply Subgroup.map_injective P.subtype_injective
    calc (commutator ↥P).map P.subtype = Z := hcommimg
      _ = centerOf P := hcenter.symm
      _ = (Subgroup.center ↥P).map P.subtype := hmapc.symm
  · rw [hfr]
    apply Subgroup.map_injective P.subtype_injective
    rw [MonoidHom.map_closure, hmapc, hcenter]
    refine le_antisymm ?_ ?_
    · rw [Subgroup.closure_le]
      rintro _ ⟨y, hy, rfl⟩
      rcases hy with hy | hy
      · rw [← hcommimg]
        exact Subgroup.mem_map_of_mem P.subtype hy
      · obtain ⟨w, rfl⟩ := hy
        exact hsq w.1 w.2
    · intro z hz
      rw [← hcommimg] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact Subgroup.subset_closure ⟨y, Or.inl hy, rfl⟩
  · intro z hz
    have hzC : (z : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨w, hw⟩)
    have hzZ : (z : G) ∈ Z := by
      rw [← hcenter]
      exact Subgroup.mem_inf.mpr ⟨z.2, hzC⟩
    have h := hZelem.2 (z : G) hzZ
    exact Subtype.ext (by simpa using h)

private theorem Gi_le_normalizer_centerOf_Q (X : Setup Γ G) (i : ℤ) :
    X.Gi i ≤ Subgroup.normalizer (centerOf (X.Q i) : Set G) :=
  (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi i)).trans
    (CFSG.Quasithin.normalizer_le_normalizer_centerOf (X.Q i))

private theorem edgeSylow_zero_le_sup_Q_one (X : Setup Γ G) {C : Subgroup G}
    (hCE : C ≤ X.edgeSylow 0) (hCnC : X.K ≤ Subgroup.normalizer (C : Set G))
    (hCQ1 : ¬ C ≤ X.Q 1) : X.edgeSylow 0 ≤ C ⊔ X.Q 1 := by
  have hCL1 : C ≤ X.L 1 := hCE.trans (X.isSylowTwoOf_edgeSylow_L_succ 0).1
  have hQ1L1 : X.Q 1 ≤ X.L 1 := X.Q_le_L 1
  obtain ⟨S, K', hSmap, hKmap, hKS, hsup⟩ :=
    exists_edgeTorusSylow X.hyp (α := X.vert 1) (β := X.vert 0) (X.adj 0).symm
      (K := X.K) (le_inf (X.K_le_Gi 1) (X.K_le_Gi 0))
      (by
        rw [show X.Gi 1 ⊓ X.Gi 0 = X.Gi 0 ⊓ X.Gi 1 from inf_comm _ _]
        exact X.K_inf_edgeSylow 0)
      (by
        rw [show X.Gi 1 ⊓ X.Gi 0 = X.Gi 0 ⊓ X.Gi 1 from inf_comm _ _]
        exact X.K_sup_edgeSylow 0)
  have hNloc := X.hyp.isLocL2_oTwoPrime (X.vert 1)
  have hval := X.hyp.valency (X.vert 1)
  have htorus : ∀ (x y : ↥(X.L 1)), x ∈ (S : Subgroup ↥(X.L 1)) →
      y ∈ (S : Subgroup ↥(X.L 1)) → (x : G) ∉ X.Q 1 → (y : G) ∉ X.Q 1 →
      ∃ k : K', ((k : ↥(X.L 1)) * x * (k : ↥(X.L 1))⁻¹ * y⁻¹) ∈
        (X.Q 1).subgroupOf (X.L 1) := by
    intro x y hxS hyS hxQ hyQ
    exact hNloc.torus_transitive_on_sylow X.hyp.adj_smul
      (X.hyp.finite_stab (X.vert 1)) hval.2 hval.1 S K' hKS hsup hxS hyS hxQ hyQ
  have hK'n : K' ≤ Subgroup.normalizer ((S : Subgroup ↥(X.L 1)) : Set ↥(X.L 1)) := by
    rw [← hsup]; exact le_sup_left
  obtain ⟨c, hcC, hcQ1⟩ := Set.not_subset.mp hCQ1
  have hcE : c ∈ X.edgeSylow 0 := hCE hcC
  have hEdge : X.edgeSylow 0 = pCoreOf 2 (X.Gi 1 ⊓ X.Gi 0) := by
    rw [show X.Gi 1 ⊓ X.Gi 0 = X.Gi 0 ⊓ X.Gi 1 from inf_comm _ _]
    rfl
  obtain ⟨s, hsS, hsc⟩ := Subgroup.mem_map.mp (by
    rw [hSmap, ← hEdge]
    exact hcE)
  have hsQN : s ∉ (X.Q 1).subgroupOf (X.L 1) := by
    intro hs
    apply hcQ1
    rw [← hsc]
    exact Subgroup.mem_subgroupOf.mp hs
  have hSsup : (S : Subgroup ↥(X.L 1)) ≤
      C.subgroupOf (X.L 1) ⊔ (X.Q 1).subgroupOf (X.L 1) := by
    intro y hy
    by_cases hyQ : y ∈ (X.Q 1).subgroupOf (X.L 1)
    · exact Subgroup.mem_sup_right hyQ
    · obtain ⟨k, hkq⟩ := htorus s y hsS hy hsQN hyQ
      let kL : ↥(X.L 1) := (k : ↥K')
      have hkK : (kL : G) ∈ X.K := by
        have hmem : (kL : G) ∈ K'.map (X.L 1).subtype :=
          Subgroup.mem_map_of_mem (X.L 1).subtype k.2
        rw [hKmap] at hmem
        exact (Subgroup.mem_inf.mp hmem).1
      have hAconj : (kL : G) * c * (kL : G)⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hCnC hkK) c).mp hcC
      have hAS : (kL * s * kL⁻¹) ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hK'n k.2) s).mp hsS
      have hAC : (kL * s * kL⁻¹) ∈ C.subgroupOf (X.L 1) := by
        rw [Subgroup.mem_subgroupOf]
        show (kL : G) * (s : G) * (kL : G)⁻¹ ∈ C
        have hsG : (s : G) = c := hsc
        rw [hsG]
        exact hAconj
      have hkq' : ((kL * s * kL⁻¹) * y⁻¹) ∈ (X.Q 1).subgroupOf (X.L 1) := hkq
      have hy_eq : y = ((kL * s * kL⁻¹) * y⁻¹)⁻¹ * (kL * s * kL⁻¹) := by group
      rw [hy_eq]
      rw [show C.subgroupOf (X.L 1) ⊔ (X.Q 1).subgroupOf (X.L 1) =
        (X.Q 1).subgroupOf (X.L 1) ⊔ C.subgroupOf (X.L 1) from sup_comm _ _]
      exact Subgroup.mul_mem_sup (((X.Q 1).subgroupOf (X.L 1)).inv_mem hkq') hAC
  have hmap := Subgroup.map_mono hSsup (f := (X.L 1).subtype)
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCL1,
    inf_eq_left.mpr hQ1L1] at hmap
  rw [hSmap, ← hEdge] at hmap
  exact hmap

private theorem centerOf_Q0_le_Q1 (X : Setup Γ G)
    (A : X.CaseA) : centerOf (X.Q 0) ≤ X.Q 1 := by
  classical
  set C : Subgroup G := centerOf (X.Q 0) with hCdef
  by_contra hnot
  have hCQ0 : C ≤ X.Q 0 := by rw [hCdef]; exact inf_le_left
  have hCnC : X.K ≤ Subgroup.normalizer (C : Set G) :=
    (X.K_le_Gi 0).trans (X.Gi_le_normalizer_centerOf_Q 0)
  have hedge : X.edgeSylow 0 ≤ C ⊔ X.Q 1 :=
    X.edgeSylow_zero_le_sup_Q_one (hCQ0.trans (X.Q_le_edgeSylow_left 0)) hCnC hnot
  have h3 := X.caseA_3 A
  have hnatZ : NatQuot (X.L 1) (X.Z 1) ⊥ (X.n 1) := h3.2.2.2.2.2.1
  have hZ1card : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 1) := by
    rw [← Subgroup.relIndex_bot_left (H := X.Z 1), hnatZ.index]
  have hZ1ne : X.Z 1 ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ1card
    exact (Nat.one_lt_two_pow (by have := A.hyp.two_le_n 1; omega)).ne' hZ1card.symm
  have hZ1Q0 : X.Z 1 ≤ X.Q 0 := X.Z_le_Q_of_lt A.b₁ (j := 0) (by norm_num)
  have hZ1Q1 : X.Z 1 ≤ Subgroup.centralizer (X.Q 1 : Set G) :=
    (X.Z_le_center 1).trans inf_le_right
  have hZ1cenC : X.Z 1 ≤ Subgroup.centralizer (C : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro c' hc'
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc').2 z (hZ1Q0 hz)).symm
  have hZ1cenEdge : X.Z 1 ≤ Subgroup.centralizer (X.edgeSylow 0 : Set G) :=
    Subgroup.le_centralizer_iff.mpr <| hedge.trans <|
      sup_le (Subgroup.le_centralizer_iff.mp hZ1cenC) (Subgroup.le_centralizer_iff.mp hZ1Q1)
  obtain ⟨t, ht, htref⟩ := X.exists_reflection A.hyp 1
  have htG1 : t ∈ X.Gi 1 := (Subgroup.mem_inf.mp ht).1
  have ht0 : t • X.vert 0 = X.vert 2 := by
    have h := htref (-1)
    rwa [show (1 : ℤ) + (-1) = 0 by norm_num, show (1 : ℤ) - (-1) = 2 by norm_num] at h
  have hS1 : X.edgeSylow 1 = conjSub t (X.edgeSylow 0) := by
    change pCoreOf 2 (X.Gi 1 ⊓ X.Gi 2) = conjSub t (pCoreOf 2 (X.Gi 0 ⊓ X.Gi 1))
    rw [← pCoreOf_conjSub, conjSub_inf, conjSub_eq_of_mem htG1, ← X.Gi_smul X ht0, inf_comm]
  have hZ1cenS1 : X.Z 1 ≤ Subgroup.centralizer (X.edgeSylow 1 : Set G) := by
    have h := conjSub_mono t hZ1cenEdge
    rwa [X.Z_normal 1 t htG1, ← conjSub_centralizer, ← hS1] at h
  have hZ1center : X.Z 1 ≤ centerOf (X.L 1) :=
    X.le_centerOf_L A.hyp.char 1 ((X.Z_le_Q 1).trans (X.Q_le_Gi 1))
      (Subgroup.le_centralizer_iff.mp hZ1cenEdge) (Subgroup.le_centralizer_iff.mp hZ1cenS1)
  have hZ1bot : X.Z 1 = ⊥ := by
    rw [h3.2.2.2.2.1] at hZ1center
    exact le_bot_iff.mp hZ1center
  exact hZ1ne hZ1bot

private theorem centerOf_Q0_le_Z0_of_le_Q2
    (X : Setup Γ G) (A : X.CaseA) (hC2 : centerOf (X.Q 0) ≤ X.Q 2) :
    centerOf (X.Q 0) ≤ X.Z 0 := by
  classical
  have h3 := X.caseA_3 A
  obtain ⟨t, ht, htref⟩ := X.exists_reflection A.hyp 0
  have htG0 : t ∈ X.Gi 0 := (Subgroup.mem_inf.mp ht).1
  have hCt : conjSub t (centerOf (X.Q 0)) = centerOf (X.Q 0) :=
    mem_normalizer_iff_conjSub.mp (X.Gi_le_normalizer_centerOf_Q 0 htG0)
  have ht2 : t • X.vert 2 = X.vert (-2) := by
    have h := htref 2
    rwa [show (0 : ℤ) + 2 = 2 by norm_num, show (0 : ℤ) - 2 = -2 by norm_num] at h
  have hQconj : conjSub t (X.Q 2) = X.Q (-2) := (X.Q_smul X ht2).symm
  have hCQ2' : centerOf (X.Q 0) ≤ X.Q (-2) := by
    have h := conjSub_mono t hC2
    rwa [hCt, hQconj] at h
  have hCGi3 : centerOf (X.Q 0) ≤ X.Gi (-3) :=
    hCQ2'.trans ((X.Q_le_Gi_adj (-2)).trans inf_le_left)
  have hCGi3' : centerOf (X.Q 0) ≤ X.Gi 3 :=
    hC2.trans ((X.Q_le_Gi_adj 2).trans inf_le_right)
  have hCarc : centerOf (X.Q 0) ≤ X.arcStab (-3) 3 := by
    rw [X.arcStab_eq_inf (by norm_num : (-3 : ℤ) ≤ 3)]
    exact le_inf hCGi3 hCGi3'
  have hCgroup : IsPGroup 2 (centerOf (X.Q 0)) :=
    (pCoreOf_isPGroup' (X.Gi 0)).to_le inf_le_left
  have hZ0fix : X.Z 0 ≤ X.arcStab (-3) 3 := by
    rw [X.arcStab_eq_inf (by norm_num : (-3 : ℤ) ≤ 3)]
    exact le_inf (by simpa using h3.1.1 (-3) (by norm_num))
      (by simpa using h3.1.1 3 (by norm_num))
  have hZ0ne : X.Z 0 ≠ ⊥ := by
    intro h
    have hc := h3.2.2.2.1
    rw [h, Subgroup.card_bot] at hc
    exact (Nat.one_lt_two_pow (by have := A.hyp.two_le_n 1; omega)).ne' hc.symm
  have hZ02 : IsPGroup 2 (X.Z 0) := (pCoreOf_isPGroup' (X.Gi 0)).to_le (X.Z_le_Q 0)
  have hZ0n : X.K ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    fun k hk => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 k (X.K_le_Gi 0 hk))
  have hZ0leP : X.Z 0 ≤ pCoreOf 2 (X.arcStab (-3) 3) :=
    X.le_pCoreOf_arcStab_r A.hyp (a := -3) hZ02 (by simpa using hZ0fix)
  have hPeq : pCoreOf 2 (X.arcStab (-3) 3) = X.Z 0 :=
    (X.eq_of_le_pCoreOf_arcStab_r A.hyp (a := -3) hZ0n hZ0ne hZ0leP).symm
  have hCleP : centerOf (X.Q 0) ≤ pCoreOf 2 (X.arcStab (-3) 3) :=
    X.le_pCoreOf_arcStab_r A.hyp (a := -3) hCgroup (by simpa using hCarc)
  rwa [hPeq] at hCleP

private theorem centerOf_Q0_le_Q2
    (X : Setup Γ G) (A : X.CaseA) : centerOf (X.Q 0) ≤ X.Q 2 := by
  have h5d := X.caseA_5d A
  have h5f := X.caseA_5f A
  have hnatZ : NatQuot (X.L 1) (X.Z 1) ⊥ (X.n 1) := (X.caseA_3 A).2.2.2.2.2.1
  have hZ1ne : X.Z 1 ≠ ⊥ := by
    intro h
    have hc : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 1) := by
      rw [← Subgroup.relIndex_bot_left (H := X.Z 1), hnatZ.index]
    rw [h, Subgroup.card_bot] at hc
    exact (Nat.one_lt_two_pow (by have := A.hyp.two_le_n 1; omega)).ne' hc.symm
  have hDleA1 : X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) ≤ X.Q 0 ⊓ X.Q 2 :=
    h5d.1.symm ▸ le_sup_left
  have hne : ⁅X.Q 0 ⊓ X.Q 2, X.Q 1⁆ ≠ ⊥ := by
    intro hbot
    apply hZ1ne
    rw [← h5f.1]
    exact le_bot_iff.mp ((Subgroup.commutator_mono hDleA1 le_rfl).trans (le_of_eq hbot))
  exact (X.caseA_w1Hyp A).centerOf_Q_zero_le_Q_two (centerOf_Q0_le_Q1 X A)
    (fun x hx y hy => h5d.2.2.2.1.comm hx hy) hne

theorem caseA_5g (X : Setup Γ G) (A : X.CaseA) :
    centerOf (X.Q 0) = X.Z 0 ∧ IsSpecialPGroup 2 ↥(X.Q 0) ∧
      IsElemSec (X.Z 0) (X.Q 0) := by
  have h3 := X.caseA_3 A
  have h5a := X.caseA_5a A
  have h5d := X.caseA_5d A
  obtain ⟨hVleQ0, hVQ0, hZ0VV, hsecV, -, -⟩ := h5a
  obtain ⟨hA1eq, -, -, hA1elem, -, hQ0eqVD⟩ := h5d
  have hnatZ : NatQuot (X.L 1) (X.Z 1) ⊥ (X.n 1) := h3.2.2.2.2.2.1
  have hZ1elem : IsElemAbelian 2 (X.Z 1) := X.isElemAbelian_Z_of_natQuot 1 hnatZ
  have hZ1eq : X.Z 1 = X.Z 0 ⊔ X.Z 2 := h3.2.2.2.2.2.2.1
  have hZ0leZ1 : X.Z 0 ≤ X.Z 1 := by rw [hZ1eq]; exact le_sup_left
  have hZ0elem : IsElemAbelian 2 (X.Z 0) :=
    CFSG.Quasithin.F7.isElemAbelian_mono hZ1elem hZ0leZ1
  set V : Subgroup G := ⨆ g ∈ X.Gi 0, conjSub g (X.Z 1) with hVdef
  set D : Subgroup G := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hDdef
  have hQ0eq : X.Q 0 = V ⊔ D := by rw [hVdef, hDdef]; exact hQ0eqVD
  have hDelem : IsElemAbelian 2 D :=
    CFSG.Quasithin.F7.isElemAbelian_mono hA1elem (by rw [hA1eq]; exact le_sup_left)
  have hVnorm : X.Gi 0 ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.Quasithin.MS93.le_normalizer_iSup_conj (X.Gi 0) (X.Z 1)
  have hsecQ0 : IsElemSec (X.Z 0) (X.Q 0) :=
    isElemSec_Q_zero_of_eq_sup X V D hQ0eq hVQ0 hsecV.2.2 hDelem
      ((le_sup_right.trans hQ0eq.ge).trans ((X.Q_le_Gi 0).trans hVnorm))
  have hZ0Q0 : X.Z 0 ≤ ⁅X.Q 0, X.Q 0⁆ :=
    hZ0VV.trans (Subgroup.commutator_mono hVleQ0 hVleQ0)
  have hcenter : centerOf (X.Q 0) = X.Z 0 := by
    have hcle : centerOf (X.Q 0) ≤ X.Z 0 :=
      centerOf_Q0_le_Z0_of_le_Q2 X A (centerOf_Q0_le_Q2 X A)
    exact le_antisymm hcle (X.Z_le_center 0)
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi 0)
  refine ⟨hcenter, ?_, hsecQ0⟩
  exact isSpecialPGroup_of_centerOf_eq (P := X.Q 0) (pCoreOf_isPGroup' (X.Gi 0))
    hZ0elem hcenter hsecQ0.2.2 (le_antisymm hsecQ0.2.1 hZ0Q0)

private theorem caseA_5g_isSpecialPow (X : Setup Γ G)
    (A : X.CaseA) (hn : ∀ i : ℤ, X.n i = 2) :
    centerOf (X.Q 0) = X.Z 0 ∧ IsSpecialPow 2 (2 ^ 2) 2 ↥(X.Q 0) := by
  have h5g := X.caseA_5g A
  have h3 := X.caseA_3 A
  have hcardZ0 : Nat.card ↥(X.Z 0) = 4 := by
    have h := h3.2.2.2.1
    rw [hn 1] at h
    exact h
  have hcardQ0 : Nat.card ↥(X.Q 0) = 2 ^ 10 := by
    have h := (X.caseA_card A).2 0
    rw [show (0 : ℤ) + 1 = 1 by norm_num, hn 0, hn 1] at h
    exact h
  have hcenter : Nat.card (Subgroup.center ↥(X.Q 0)) = 4 := by
    have h := Subgroup.card_map_of_injective (K := Subgroup.center ↥(X.Q 0))
      (f := (X.Q 0).subtype) (X.Q 0).subtype_injective
    rw [CFSG.Quasithin.F6.map_center_eq_centerOf] at h
    rw [← h, h5g.1, hcardZ0]
  refine ⟨h5g.1, h5g.2.1, ?_, ?_⟩
  · rw [hcardQ0]
    norm_num
  · rw [hcenter]
    norm_num

private theorem caseA_centerOf_Q_one_le
    (X : Setup Γ G) (A : X.CaseA) (hA1Q1 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1)
    (hcommQQ : ⁅X.Q 1, X.Q 1⁆ = X.Z 1) (hZ1ne : X.Z 1 ≠ ⊥) :
    centerOf (X.Q 1) ≤ X.Q 0 ⊓ X.Q 2 := by
  have hW := X.caseA_w1Hyp A
  have hAcomm : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2) := (X.caseA_5d A).2.2.2.1
  have hLCeq : X.L 1 ≤ Subgroup.normalizer (centerOf (X.Q 1) : Set G) :=
    (X.L_le_Gi 1).trans (X.Gi_le_normalizer_centerOf_Q 1)
  set C := centerOf (X.Q 1) with hCdef
  have hCQ : C ≤ X.Q 1 := inf_le_left
  have hCcent : ∀ c ∈ C, ∀ q ∈ X.Q 1, c * q = q * c := by
    intro c hc q hq
    rw [hCdef] at hc
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) q hq).symm
  have hLA : X.L 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
    (X.L_le_Gi 1).trans (X.caseA_5b A).1
  have hLnorm : X.L 1 ≤
      Subgroup.normalizer ((C ⊔ (X.Q 0 ⊓ X.Q 2) : Subgroup G) : Set G) := by
    intro l hl
    have hCconj : conjSub l C = C := mem_normalizer_iff_conjSub.mp (hLCeq hl)
    have hAconj : conjSub l (X.Q 0 ⊓ X.Q 2) = X.Q 0 ⊓ X.Q 2 :=
      mem_normalizer_iff_conjSub.mp (hLA hl)
    rw [mem_normalizer_iff_conjSub]
    rw [conjSub_sup, hCconj, hAconj]
  have hKinvC : ∀ k ∈ X.K, conjSub k C = C := fun k hk =>
    mem_normalizer_iff_conjSub.mp (X.Gi_le_normalizer_centerOf_Q 1 (X.K_le_Gi 1 hk))
  have hKinvA1 : ∀ k ∈ X.K, conjSub k (X.Q 0 ⊓ X.Q 2) = X.Q 0 ⊓ X.Q 2 := fun k hk =>
    mem_normalizer_iff_conjSub.mp ((X.caseA_5b A).1 (X.K_le_Gi 1 hk))
  have hKnorm : X.K ≤
      Subgroup.normalizer ((C ⊔ (X.Q 0 ⊓ X.Q 2) : Subgroup G) : Set G) := by
    intro k hk
    rw [mem_normalizer_iff_conjSub, conjSub_sup, hKinvC k hk, hKinvA1 k hk]
  have hGinorm : X.Gi 1 ≤
      Subgroup.normalizer ((C ⊔ (X.Q 0 ⊓ X.Q 2) : Subgroup G) : Set G) := by
    rw [X.Gi_eq_L_sup_K 1]
    exact sup_le hLnorm hKnorm
  rcases hW.irred (C ⊔ (X.Q 0 ⊓ X.Q 2)) le_sup_right
    (sup_le hCQ hA1Q1) hGinorm with h | h
  · rw [← h]
    exact le_sup_left
  · exfalso
    have habel : IsMulCommutative ↥(X.Q 1) := by
      rw [← h]
      have hunion : C ⊔ (X.Q 0 ⊓ X.Q 2) =
          Subgroup.closure ((C : Set G) ∪ ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G)) := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      rw [hunion]
      refine Subgroup.isMulCommutative_closure ?_
      intro x hx y hy _
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hCcent x hx y (hCQ hy)
      · exact hCcent x hx y (hA1Q1 hy)
      · exact (hCcent y hy x (hA1Q1 hx)).symm
      · exact hAcomm.comm hx hy
    have hbot : ⁅X.Q 1, X.Q 1⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr habel
    rw [hcommQQ] at hbot
    exact hZ1ne hbot

private theorem caseA_centerOf_Q_one_eq
    (X : Setup Γ G) (A : X.CaseA) (hCmem : centerOf (X.Q 1) ≤ X.Q 0 ⊓ X.Q 2) :
    centerOf (X.Q 1) = X.Z 1 := by
  have h5d := X.caseA_5d A
  have h5f := X.caseA_5f A
  have hAcomm : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2) := h5d.2.2.2.1
  have hZA : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [h5d.1]
    exact le_sup_right
  refine le_antisymm ?_ (X.Z_le_center 1)
  set C := centerOf (X.Q 1) with hCdef
  have hZleC : X.Z 1 ≤ C := by
    rw [hCdef]
    exact X.Z_le_center 1
  have hCD : C ⊓ (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc C ⊓ (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G))
        ≤ Subgroup.centralizer (X.Q 1 : Set G) ⊓
            (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) :=
          inf_le_inf_right _ (show C ≤ Subgroup.centralizer (X.Q 1 : Set G) from by
            rw [hCdef]; exact inf_le_right)
      _ = ⊥ := by rw [inf_comm]; exact h5f.2
  have hCZ : C ⊓ ((X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1) ≤ X.Z 1 := by
    intro x hx
    obtain ⟨hxC, hxsup⟩ := Subgroup.mem_inf.mp hx
    have hDA : (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ≤ X.Q 0 ⊓ X.Q 2 :=
      h5d.1.symm ▸ le_sup_left
    have hDZnorm : (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ≤
        Subgroup.normalizer (X.Z 1 : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer (X.Z 1 : Set G))
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact hAcomm.comm (hZA hz) (hDA hd)
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right
      (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) (X.Z 1) hDZnorm
    have hxmul : x ∈ ((X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) : Subgroup G) : Set G) *
        (X.Z 1 : Set G) := by
      rw [← hcoe]
      exact hxsup
    obtain ⟨d, hd, z, hz, hdz⟩ := hxmul
    have hzC : z ∈ C := hZleC hz
    have hdC : d ∈ C := by
      have he : d = x * z⁻¹ := by rw [← hdz]; group
      rw [he]
      exact C.mul_mem hxC (C.inv_mem hzC)
    have hdbot : d ∈ (⊥ : Subgroup G) := by
      rw [← hCD]
      exact Subgroup.mem_inf.mpr ⟨hdC, hd⟩
    rw [Subgroup.mem_bot.mp hdbot] at hdz
    simp only [one_mul] at hdz
    rwa [← hdz]
  have hCe : C = X.Z 1 := by
    calc C = C ⊓ (X.Q 0 ⊓ X.Q 2) := (inf_eq_left.mpr hCmem).symm
      _ = C ⊓ ((X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1) := by rw [h5d.1]
      _ = X.Z 1 := le_antisymm hCZ (le_inf hZleC le_sup_right)
  exact hCe.le

theorem caseA_5k (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    centerOf (X.Q 1) = X.Z 1 ∧ IsSpecialPGroup 2 ↥(X.Q 1) ∧
      IsElemSec (X.Z 1) (X.Q 1) := by
  have h5c := X.caseA_5c A hn
  have h5d := X.caseA_5d A
  have h5f := X.caseA_5f A
  have hnat1 : NatQuot (X.L 1) (X.Z 1) ⊥ (X.n 1) := (X.caseA_3 A).2.2.2.2.2.1
  have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  have hZA : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [h5d.1]
    exact le_sup_right
  have hAcomm : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2) := h5d.2.2.2.1
  have hZ1elem : IsElemAbelian 2 (X.Z 1) := F7.isElemAbelian_mono hAcomm hZA
  have hsecA : IsElemSec (X.Q 0 ⊓ X.Q 2) (X.Q 1) := by
    have h := X.Q_quot A.hyp.char A.hyp.sing (by have h5 := A.hyp.five_le; omega) 1
    refine ⟨?_, ?_, ?_⟩
    · simpa using h.1
    · simpa using h.2.2.1
    · intro x hx
      simpa using h.2.1 x hx
  have hsecZ : IsElemSec (X.Z 1) (X.Q 0 ⊓ X.Q 2) := by
    refine ⟨hZA, ?_, ?_⟩
    · rw [Subgroup.commutator_self_eq_bot_iff.mpr hAcomm.1]
      exact bot_le
    · intro e he
      rw [hAcomm.2 e he]
      exact (X.Z 1).one_mem
  have hsec : IsElemSec (X.Z 1) (X.Q 1) := by
    haveI : Finite ↥(X.L 1) := finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
    refine isElemSec_of_natQuot_center (L := X.L 1) (E := X.Q 1) (Z := X.Q 0 ⊓ X.Q 2)
      (N := X.Z 1) ?_ (pCoreOf_isPGroup' (X.Gi 1)) h5c.1 hsecA hsecZ
      h5d.2.2.2.2.1
    · have h := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).quot
      rwa [show nOf Γ (X.vert 1) = 2 from hn 1] at h
  have hcommQQ : ⁅X.Q 1, X.Q 1⁆ = X.Z 1 := by
    refine le_antisymm hsec.2.1 ?_
    calc X.Z 1 = ⁅X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G), X.Q 1⁆ := h5f.1.symm
      _ ≤ ⁅X.Q 1, X.Q 1⁆ := Subgroup.commutator_mono inf_le_left le_rfl
  have hcardZ1 : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 1) := by
    rw [← Subgroup.relIndex_bot_left (H := X.Z 1), hnat1.index]
  have hZ1ne : X.Z 1 ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcardZ1
    exact (Nat.one_lt_two_pow (by have := A.hyp.two_le_n 1; omega)).ne' hcardZ1.symm
  have hcenter : centerOf (X.Q 1) = X.Z 1 :=
    X.caseA_centerOf_Q_one_eq A (X.caseA_centerOf_Q_one_le A hsecA.1 hcommQQ hZ1ne)
  haveI : Finite ↥(X.Q 1) := finite_of_le_stabilizer X.hyp (H := X.Q 1) (X.Q_le_Gi 1)
  exact ⟨hcenter, isSpecialPGroup_of_centerOf_eq (P := X.Q 1) (pCoreOf_isPGroup' (X.Gi 1))
    hZ1elem hcenter hsec.2.2 hcommQQ, hsec⟩

private theorem caseA_card_edge (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) = 2 ^ 12 * 3 ^ 2 := by
  obtain ⟨-, hZ0c, -, hcardZ0, -, hnat1, hZ1eq, -⟩ := X.caseA_3 A
  have hZ0ne : X.Z 0 ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardZ0
    exact (Nat.one_lt_two_pow (by have := A.hyp.two_le_n 1; omega)).ne' hcardZ0.symm
  have h0 : X.Z 0 ≤ Subgroup.centralizer (X.Ki 0 : Set G) := by
    rw [hZ0c]
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp hz.2) k (Subgroup.mem_inf.mp hk).2
  have h1 : ∀ k ∈ X.Ki 1, k ≠ 1 → ∀ u ∈ X.Z 0, k * u = u * k → u = 1 := by
    intro k hk hk1 u hu hcomm
    have hkK : k ∈ X.K := (Subgroup.mem_inf.mp hk).1
    have hkL : k ∈ X.L 1 := (Subgroup.mem_inf.mp hk).2
    have hkodd : Odd (orderOf k) :=
      Odd.of_dvd_nat X.odd_card_K (Subgroup.orderOf_dvd_natCard X.K hkK)
    have hknotZ : k ∉ X.Z 1 := by
      intro hkZ
      have hmem : k ∈ X.K ⊓ X.Q 1 :=
        Subgroup.mem_inf.mpr ⟨hkK, X.Z_le_Q 1 hkZ⟩
      rw [X.K_inf_Q_eq_bot 1] at hmem
      exact hk1 (Subgroup.mem_bot.mp hmem)
    have huZ : u ∈ X.Z 1 := by
      rw [hZ1eq]
      exact Subgroup.mem_sup_left hu
    have hcomm' : ⁅u, k⁆ ∈ (⊥ : Subgroup G) := by
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.symm
    have hbot := hnat1.fpf k hkL hkodd hknotZ u huZ hcomm'
    rwa [Subgroup.mem_bot] at hbot
  have hKi : X.Ki 0 ⊓ X.Ki 1 = ⊥ :=
    X.Ki_inf_eq_bot_of 0 (Or.inl rfl) hZ0ne h0 h1
  rw [X.card_edge_of_Ki_inf hKi, (X.caseA_card A).1, hn 0, hn 1]
  norm_num

theorem caseA_comm_D_Ki_zero
    (X : Setup Γ G) (A : X.CaseA) :
    ⁅X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G), X.Ki 0⁆ =
      X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) := by
  have h5d := X.caseA_5d A
  have h5e := X.caseA_5e A
  set D := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hDdef
  have hDP : D = pCoreOf 2 (X.arcStab (-2) ((-2) + ((6 : ℕ) : ℤ))) := by
    rw [show (-2 : ℤ) + ((6 : ℕ) : ℤ) = 4 by norm_num]
    exact h5e.1
  have hDcard : Nat.card ↥D = 2 ^ X.n 0 := h5d.2.2.1
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    exact (Nat.one_lt_two_pow (by have := A.hyp.two_le_n 0; omega)).ne' hDcard.symm
  have hDcent1 : D ≤ Subgroup.centralizer (X.Ki 1 : Set G) :=
    fun d hd => (Subgroup.mem_inf.mp hd).2
  have hconjD : ∀ k ∈ X.K, conjSub k D = D := fun k hk =>
    mem_normalizer_iff_conjSub.mp (X.K_le_normalizer_Q_inf_centralizer_Ki 1 hk)
  have hconjKi0 : ∀ k ∈ X.K, conjSub k (X.Ki 0) = X.Ki 0 := by
    intro k hk
    have hkG0 : k ∈ X.Gi 0 := X.K_le_Gi 0 hk
    have hL0 : conjSub k (X.L 0) = X.L 0 := by
      have h := conjSub_oTwoPrime k (X.Gi 0)
      rw [conjSub_eq_of_mem hkG0] at h
      exact h
    change conjSub k (X.K ⊓ X.L 0) = X.K ⊓ X.L 0
    rw [conjSub_inf, conjSub_eq_of_mem hk, hL0]
  have hCDK : D ⊓ Subgroup.centralizer (X.Ki 0 : Set G) = ⊥ := by
    by_contra hne
    set U := D ⊓ Subgroup.centralizer (X.Ki 0 : Set G) with hUdef
    have hKinv : X.K ≤ Subgroup.normalizer (U : Set G) := by
      intro k hk
      rw [mem_normalizer_iff_conjSub]
      rw [hUdef]
      change conjSub k (D ⊓ Subgroup.centralizer (X.Ki 0 : Set G)) =
        D ⊓ Subgroup.centralizer (X.Ki 0 : Set G)
      rw [conjSub_inf, hconjD k hk, ← conjSub_centralizer, hconjKi0 k hk]
    have hUle : U ≤ pCoreOf 2 (X.arcStab (-2) ((-2) + ((6 : ℕ) : ℤ))) := by
      rw [← hDP]
      exact inf_le_left
    have hUeq := X.eq_of_le_pCoreOf_arcStab_r A.hyp hKinv hne hUle
    have hDU : D = U := hDP.trans hUeq.symm
    have hDcent0 : D ≤ Subgroup.centralizer (X.Ki 0 : Set G) := by
      rw [hDU]
      exact inf_le_right
    have hKcent : X.K ≤ Subgroup.centralizer (D : Set G) := by
      rw [X.K_eq_sup]
      refine sup_le ?_ ?_
      · rw [Subgroup.le_centralizer_iff]
        exact hDcent0
      · rw [Subgroup.le_centralizer_iff]
        exact hDcent1
    obtain ⟨k, hkKi, hk1, -, -⟩ := X.exists_generator_Ki (-2) (A.hyp.two_le_n (-2))
    obtain ⟨d, hdD, hd1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hDne
    have hkK : k ∈ X.K := (Subgroup.mem_inf.mp hkKi).1
    have hcomm : k * d = d * k :=
      (Subgroup.mem_centralizer_iff.mp (hKcent hkK) d hdD).symm
    have hdP : d ∈ pCoreOf 2 (X.arcStab (-2) ((-2) + ((6 : ℕ) : ℤ))) := by
      rw [← hDP]
      exact hdD
    exact hd1 (X.Ki_fpf_pCoreOf_arcStab_r A.hyp (-2) hkKi hk1 d hdP hcomm)
  have hKi0N : X.Ki 0 ≤ Subgroup.normalizer (D : Set G) := fun k hk =>
    mem_normalizer_iff_conjSub.mpr (hconjD k (Subgroup.mem_inf.mp hk).1)
  have hcomm_le_D : ⁅D, X.Ki 0⁆ ≤ D := Subgroup.le_normalizer_iff_commutator_le_left.mp hKi0N
  have hne' : ⁅D, X.Ki 0⁆ ≠ ⊥ := by
    intro hbot
    have hle : D ≤ Subgroup.centralizer (X.Ki 0 : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hcc : D ⊓ Subgroup.centralizer (X.Ki 0 : Set G) = D := inf_eq_left.mpr hle
    rw [hCDK] at hcc
    exact hDne hcc.symm
  have hKinv2 : X.K ≤ Subgroup.normalizer (⁅D, X.Ki 0⁆ : Subgroup G) := by
    intro k hk
    rw [mem_normalizer_iff_conjSub]
    rw [← conjSub_commutator, hconjD k hk, hconjKi0 k hk]
  have hle : ⁅D, X.Ki 0⁆ ≤ pCoreOf 2 (X.arcStab (-2) ((-2) + ((6 : ℕ) : ℤ))) :=
    hcomm_le_D.trans hDP.le
  have heq := X.eq_of_le_pCoreOf_arcStab_r A.hyp hKinv2 hne' hle
  exact (hDP.trans heq.symm).symm

theorem caseA_indec_left (X : Setup Γ G) (A : X.CaseA) :
    ⁅pCoreOf 2 (X.L 0), X.L 0⁆ = pCoreOf 2 (X.L 0) := by
  have h5d := X.caseA_5d A
  have h5f := X.caseA_5f A
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  rw [hQ0]
  set D := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hDdef
  have hDA : D ≤ X.Q 0 ⊓ X.Q 2 := h5d.1.symm ▸ le_sup_left
  have hDQ : D ≤ X.Q 0 := hDA.trans inf_le_left
  have hDcomm : D = ⁅D, X.Ki 0⁆ := (X.caseA_comm_D_Ki_zero A).symm
  have hNle : ⁅X.Q 0, X.L 0⁆ ≤ X.Q 0 := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)))
  have hQ1G0 : X.Q 1 ≤ X.Gi 0 := by
    have h := X.Q_le_edgeSylow 0
    rw [show (0 : ℤ) + 1 = 1 by norm_num, X.edgeSylow_zero] at h
    exact h.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)
  have hQ1L0 : X.Q 1 ≤ X.L 0 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) hQ1G0
  have hDleN : D ≤ ⁅X.Q 0, X.L 0⁆ := by
    rw [hDcomm]
    exact Subgroup.commutator_mono hDQ inf_le_right
  have hZ1leN : X.Z 1 ≤ ⁅X.Q 0, X.L 0⁆ := by
    rw [← h5f.1]
    exact Subgroup.commutator_mono hDQ hQ1L0
  have hNconj : ∀ g ∈ X.Gi 0, conjSub g ⁅X.Q 0, X.L 0⁆ = ⁅X.Q 0, X.L 0⁆ := by
    intro g hg
    have hQ : conjSub g (X.Q 0) = X.Q 0 :=
      mem_normalizer_iff_conjSub.mp
        ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) hg)
    have hL : conjSub g (X.L 0) = X.L 0 := by
      have h := conjSub_oTwoPrime g (X.Gi 0)
      rwa [conjSub_eq_of_mem hg] at h
    change conjSub g ⁅X.Q 0, X.L 0⁆ = ⁅X.Q 0, X.L 0⁆
    rw [← conjSub_commutator, hQ, hL]
  have hVleN : (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ≤ ⁅X.Q 0, X.L 0⁆ :=
    iSup_le fun g => iSup_le fun hg => by
      have h1 : conjSub g (X.Z 1) ≤ conjSub g ⁅X.Q 0, X.L 0⁆ := Subgroup.map_mono hZ1leN
      rw [hNconj g hg] at h1
      exact h1
  have hQ0leN : X.Q 0 ≤ ⁅X.Q 0, X.L 0⁆ := by
    calc X.Q 0 = (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ⊔ D := h5d.2.2.2.2.2
      _ ≤ ⁅X.Q 0, X.L 0⁆ := sup_le hVleN hDleN
  exact le_antisymm hNle hQ0leN

theorem caseA_data (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    X.TreeG24Data := by
  have h5c := X.caseA_5c A hn
  have h5d := X.caseA_5d A
  have h5g := X.caseA_5g A
  have h5k := X.caseA_5k A hn
  have hAcard := X.caseA_card A
  have hAcard' : Nat.card X.S = 2 ^ 12 ∧
      ∀ i : ℤ, Nat.card (X.Q i) = 2 ^ 10 := by
    refine ⟨?_, ?_⟩
    · simpa [hn 0, hn 1] using hAcard.1
    · intro i
      simpa [hn i, hn (i + 1)] using hAcard.2 i
  have h3 := X.caseA_3 A
  have hnat1 : NatQuot (X.L 1) (X.Z 1) ⊥ 2 := by
    simpa [hn 1] using h3.2.2.2.2.2.1
  have hZ0c : X.Z 0 = centerOf (X.L 0) := h3.2.1
  have hQ0 : pCoreOf 2 (X.L 0) = X.Q 0 := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).pCoreOf_eq
  have hQ1 : pCoreOf 2 (X.L 1) = X.Q 1 := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).pCoreOf_eq
  have hcardZ1 : Nat.card ↥(X.Z 1) = 2 ^ 4 := by
    rw [← Subgroup.relIndex_bot_left (H := X.Z 1), hnat1.index]
  have hDcard : Nat.card ↥(X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) = 4 := by
    simpa [hn 0] using h5d.2.2.1
  have hDZ : (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊓ X.Z 1 = ⊥ := h5d.2.1
  have hAcomm : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2) := h5d.2.2.2.1
  have hAsup : X.Q 0 ⊓ X.Q 2 =
      (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1 := h5d.1
  have hZA : X.Z 1 ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [hAsup]; exact le_sup_right
  have hDA : X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) ≤ X.Q 0 ⊓ X.Q 2 := by
    rw [hAsup]; exact le_sup_left
  have hDnorm : X.Z 1 ≤ Subgroup.normalizer
      ((X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact hAcomm.comm (hDA hd) (hZA hz)
  refine ⟨hAcard'.1, X.caseA_card_edge A hn, ?_, ?_, X.caseA_indec_left A, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact hQ0 ▸ (X.caseA_5g_isSpecialPow A hn).2
  · rw [hQ0, h5g.1, hZ0c]
  · exact hQ1 ▸ hAcard'.2 1
  · exact hQ1 ▸ h5k.2.1
  · rw [hQ1, h5k.1]; exact hcardZ1
  · rw [hQ1, h5k.1]
    exact hnat1.natSec ((pCoreOf_isPGroup' (X.Gi 1)).to_le (X.Z_le_Q 1))
  · refine ⟨X.Q 0 ⊓ X.Q 2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hQ1, h5k.1, hAsup]; exact le_sup_right
    · rw [hQ1, hAsup]
      exact sup_le inf_le_left (X.Z_le_Q 1)
    · rw [hAsup]
      refine (CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) (X.Z 1) hDnorm ?_).trans ?_
      · rw [disjoint_iff]; exact hDZ
      · rw [hDcard, hcardZ1]; norm_num
    · rw [hQ1, h5k.1]; exact h5d.2.2.2.2.1
    · rw [hQ1]
      exact h5c.1.natSec (pCoreOf_isPGroup' (X.Gi 1))
  · rw [hQ0, hQ1]
    have hc := X.card_inf_of_card (V := V) (G := G) A.hyp.char
    rw [hAcard'.1, hAcard'.2 0, hAcard'.2 1] at hc
    have h2 : Nat.card ↥(X.Q 0 ⊓ X.Q 1) * 4096 = 1048576 := by simpa using hc
    have h3 : (1048576 : ℕ) = 256 * 4096 := by norm_num
    have h4 : Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 256 := by omega
    rw [show (2:ℕ)^8 = 256 by norm_num]
    exact h4

end Setup

end CFSG.Quasithin.St84
