module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalProduct
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.Defs

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}

omit [Finite G] in
theorem e6QTwoN_eq_one_of_mem_center (hZcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    {z : G} (hzL : z ∈ L) (hzc : z ∈ Subgroup.centralizer (L : Set G)) {k : ℕ}
    (hz : z ^ 3 ^ k = 1) : z = 1 := by
  have hzc' : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzc l l.2
  have hdvd3 : orderOf z ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hz
  have hdvdZ : orderOf z ∣ Nat.card (Subgroup.center ↥L) := by
    rw [Subgroup.orderOf_coe (⟨z, hzL⟩ : ↥L)]
    rw [Subgroup.orderOf_coe (⟨⟨z, hzL⟩, hzc'⟩ : Subgroup.center ↥L)]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ k) (Nat.card (Subgroup.center ↥L)) := hZcop.pow_left k
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvdZ)

theorem e6QTwoN_C0_le_sup_Z (hZcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)))
    (hBs : IsElemAbelian 3 Bs)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup.centralizer (L : Set G) ⊓ (L ⊔ Bs) ≤
      Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)) := by
  classical
  intro c hc
  set C : Subgroup G := Subgroup.centralizer (L : Set G) with hCdef
  set Z : Subgroup G := L ⊓ C with hZdef
  let M : ℕ := Nat.card (Subgroup.center ↥L)
  have hZcopM : Nat.Coprime 3 M := hZcop
  have hcC : c ∈ C := hc.1
  have hcSup : c ∈ L ⊔ Bs := hc.2
  obtain ⟨l, hl, b, hb, hclb⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing L Bs hNL c).mp hcSup
  have hb3 : b ^ 3 = 1 := hBs.2 b hb
  have hbl : b * l * b⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hNL hb) l).mp hl
  have hb2l : b ^ 2 * l * (b ^ 2)⁻¹ ∈ L := by
    have h := (Subgroup.mem_normalizer_iff.mp (hNL hb) (b * l * b⁻¹)).mp hbl
    rw [pow_two]
    convert h using 1
    group
  have hc3L : c ^ 3 ∈ L := by
    have hpow : (l * b) ^ 3 = l * b * l * b * l * b := by
      simp only [pow_succ]
      group
    have heq : c ^ 3 =
        l * (b * l * b⁻¹) * (b ^ 2 * l * (b ^ 2)⁻¹) * b ^ 3 := by
      rw [← hclb, hpow]
      simp only [pow_succ]
      group
    rw [heq, hb3]
    exact L.mul_mem (L.mul_mem (L.mul_mem hl hbl) hb2l) (Subgroup.one_mem L)
  have hc3C : c ^ 3 ∈ C := C.pow_mem hcC 3
  have hc3Z : c ^ 3 ∈ Z := Subgroup.mem_inf.mpr ⟨hc3L, hc3C⟩
  have hcardZ : Nat.card ↥Z = M := by
    have hZeq : Z = CFSG.centerIn L := by
      rw [hZdef, hCdef]
      rfl
    rw [hZeq, CFSG.centerIn_eq_map_center,
      Subgroup.card_map_of_injective L.subtype_injective]
  have hc3m : (c ^ 3) ^ M = 1 := by
    have hG : Fintype G := Fintype.ofFinite G
    have hZ : Fintype ↥Z := @Subtype.fintype G (fun z => z ∈ Z) (Classical.decPred _) hG
    have h1 : (⟨c ^ 3, hc3Z⟩ : ↥Z) ^ Fintype.card ↥Z = 1 :=
      @pow_card_eq_one ↥Z _ hZ _
    have h2 : Fintype.card ↥Z = M := by
      rw [← @Nat.card_eq_fintype_card ↥Z hZ, hcardZ]
    have h3 : (⟨c ^ 3, hc3Z⟩ : ↥Z) ^ M = 1 := by
      rw [← h2]
      exact h1
    simpa using congrArg (fun w : ↥Z => (w : G)) h3
  have hc3m_z : (c ^ 3) ^ (M : ℤ) = 1 := by
    rw [zpow_natCast]
    exact hc3m
  have hbez : (3 : ℤ) * (Nat.gcdA 3 M : ℤ) + (M : ℤ) * (Nat.gcdB 3 M : ℤ) = 1 := by
    have h := Nat.gcd_eq_gcd_ab 3 M
    have hgcd : Nat.gcd 3 M = 1 := hZcopM
    rw [hgcd] at h
    push_cast at h
    exact h.symm
  let u : ℤ := Nat.gcdA 3 M
  let v : ℤ := Nat.gcdB 3 M
  have hbez' : (3 : ℤ) * u + (M : ℤ) * v = 1 := hbez
  let d : G := c ^ ((M : ℤ) * v)
  have hzpowC : (c ^ 3) ^ (-u) ∈ C := C.zpow_mem hc3C (-u)
  have hzpowL : (c ^ 3) ^ (-u) ∈ L := L.zpow_mem hc3L (-u)
  have hc_eq : c = (c ^ 3) ^ u * d := by
    have h3u : c ^ ((3 : ℤ) * u) = (c ^ 3) ^ u := by
      simpa [zpow_natCast] using zpow_mul c (3 : ℤ) u
    calc c = c ^ (1 : ℤ) := (zpow_one c).symm
      _ = c ^ ((3 : ℤ) * u + (M : ℤ) * v) := by rw [← hbez']
      _ = c ^ ((3 : ℤ) * u) * c ^ ((M : ℤ) * v) := zpow_add _ _ _
      _ = (c ^ 3) ^ u * d := by rw [h3u]
  have hd_eq : d = (c ^ 3) ^ (-u) * c := by
    have hneg : (c ^ 3) ^ (-u) = ((c ^ 3) ^ u)⁻¹ := zpow_neg (c ^ 3) u
    rw [hneg]
    calc d = ((c ^ 3) ^ u)⁻¹ * ((c ^ 3) ^ u * d) := by group
      _ = ((c ^ 3) ^ u)⁻¹ * c := by rw [← hc_eq]
  have hdC : d ∈ C := by
    rw [hd_eq]
    exact C.mul_mem hzpowC hcC
  have hdSup : d ∈ L ⊔ Bs := by
    rw [hd_eq]
    exact (L ⊔ Bs).mul_mem (Subgroup.mem_sup_left hzpowL) hcSup
  have hd3 : d ^ 3 = 1 := by
    have hc3m_z' : (c ^ (3 : ℤ)) ^ (M : ℤ) = 1 := by
      rw [show c ^ (3 : ℤ) = c ^ 3 from zpow_natCast c 3]
      exact hc3m_z
    have hdz : d ^ (3 : ℤ) = 1 := by
      rw [show d = c ^ ((M : ℤ) * v) from rfl, ← zpow_mul]
      rw [show ((M : ℤ) * v) * 3 = 3 * ((M : ℤ) * v) by ring]
      rw [zpow_mul, zpow_mul, hc3m_z', one_zpow]
    rw [← zpow_natCast]
    exact hdz
  have hdCBs : d ∈ Subgroup.centralizer (Bs : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro b hb
    obtain ⟨l', hl', b', hb', hd_eq'⟩ :=
      (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing L Bs hNL d).mp hdSup
    have hbb' : b' * b = b * b' :=
      congrArg Subtype.val (hBs.1.is_comm.comm ⟨b', hb'⟩ ⟨b, hb⟩)
    have hb'conj : b' * b * b'⁻¹ = b := by
      rw [hbb']
      group
    have hzL : d * b * d⁻¹ * b⁻¹ ∈ L := by
      have heq : d * b * d⁻¹ * b⁻¹ = l' * (b * l'⁻¹ * b⁻¹) := by
        rw [← hd_eq']
        calc (l' * b') * b * (l' * b')⁻¹ * b⁻¹
            = l' * (b' * b * b'⁻¹) * l'⁻¹ * b⁻¹ := by group
          _ = l' * b * l'⁻¹ * b⁻¹ := by rw [hb'conj]
          _ = l' * (b * l'⁻¹ * b⁻¹) := by group
      rw [heq]
      exact L.mul_mem hl'
        ((Subgroup.mem_normalizer_iff.mp (hNL hb) l'⁻¹).mp (L.inv_mem hl'))
    have hCN : Bs ≤ Subgroup.normalizer (C : Set G) :=
      hNL.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup L)
    have hzC : d * b * d⁻¹ * b⁻¹ ∈ C := by
      have hb_dinv : b * d⁻¹ * b⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hCN hb) d⁻¹).mp (C.inv_mem hdC)
      have heq : d * b * d⁻¹ * b⁻¹ = d * (b * d⁻¹ * b⁻¹) := by group
      rw [heq]
      exact C.mul_mem hdC hb_dinv
    have hzZ : d * b * d⁻¹ * b⁻¹ ∈ Z := Subgroup.mem_inf.mpr ⟨hzL, hzC⟩
    set z : G := d * b * d⁻¹ * b⁻¹ with hzdef
    have hdz_comm : Commute d z := by
      have h := Subgroup.mem_centralizer_iff.mp hdC z hzZ.1
      exact h.symm
    have hzconj : d * b * d⁻¹ = z * b := by
      rw [hzdef]
      group
    have hstep : ∀ k : ℕ, d ^ k * b * (d ^ k)⁻¹ = z ^ k * b := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          have hdk : d * z ^ k * d⁻¹ = z ^ k := by
            rw [hdz_comm.pow_right k]
            group
          calc d ^ (k + 1) * b * (d ^ (k + 1))⁻¹
              = d * (d ^ k * b * (d ^ k)⁻¹) * d⁻¹ := by group
            _ = d * (z ^ k * b) * d⁻¹ := by rw [ih]
            _ = (d * z ^ k * d⁻¹) * (d * b * d⁻¹) := by group
            _ = z ^ k * (d * b * d⁻¹) := by rw [hdk]
            _ = z ^ k * (z * b) := by rw [hzconj]
            _ = z ^ (k + 1) * b := by rw [pow_succ]; group
    have hz3 : z ^ 3 = 1 := by
      have h3 := hstep 3
      rw [hd3, inv_one, mul_one, one_mul] at h3
      have h4 : z ^ 3 * b = 1 * b := by
        rw [one_mul]
        exact h3.symm
      exact mul_right_cancel h4
    have hz1 : z = 1 :=
      e6QTwoN_eq_one_of_mem_center (k := 1) hZcop hzL hzC (by simpa using hz3)
    have hbd : b * d = d * b := by
      rw [hzdef] at hz1
      calc b * d = (d * b * d⁻¹ * b⁻¹) * (b * d) := by rw [hz1, one_mul]
        _ = d * b := by group
    exact hbd
  have hdBs : d ∈ Bs := hstar d hdCBs hd3
  rw [hc_eq]
  exact (Bs ⊔ (L ⊓ C)).mul_mem (Subgroup.mem_sup_right (Z.zpow_mem hc3Z u))
    (Subgroup.mem_sup_left hdBs)

end CFSG.StandardType.E6QTwo
