module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndConj
public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndComp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.Symplectic CFSG.Open CFSG.StandardType.SpJoin
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]

theorem spEnd_exists_endNode_of_compatible_lifts {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : 3 ≤ m) {x y : G} {L K : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hK : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K)
    (φ₁ φ₂ : StatedSp (m + 1) F →* G) (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
    (hL' : φ₁.range = L) (hK' : φ₂.range = K)
    (hβ : ∀ h : StatedSp m F, φ₁ (spLeviBlock m F h) = φ₂ (spLeviBlock m F h))
    {g : SpecialLinearGroup (Fin 2) F} (hg : g ^ p = 1) (hg1 : g ≠ 1)
    (hy : y = φ₁ (lam (0 : Fin (m + 1)) g)) {k : ℕ} (hx : x = φ₂ (lam (0 : Fin (m + 1)) (g ^ k)))
    (hx1 : x ≠ 1) :
    ∃ T : G, T ∈ L ⊔ K ∧ GGSpEndNode φ₁ T ∧ K = L.map (MulAut.conj T).toMonoidHom := by
  have h2 : (2 : F) = 0 := by simpa using (CharP.cast_eq_zero F 2)
  haveI : Fact p.Prime := ⟨hp⟩
  let n0 : StatedSp (m + 1) F := weylRep (m + 1) F 0
  let a : G := φ₁ n0
  let b : G := φ₂ n0
  have hsp : n0 * n0 = 1 := by
    change weylRep (m + 1) F 0 * weylRep (m + 1) F 0 = 1
    exact spWeylRep_mul_self (m + 1) h2 0
  have haa : a * a = 1 := by
    change φ₁ n0 * φ₁ n0 = 1
    rw [← map_mul, hsp, map_one]
  have hbb : b * b = 1 := by
    change φ₂ n0 * φ₂ n0 = 1
    rw [← map_mul, hsp, map_one]
  have hTT : (a * b * a) * (a * b * a) = 1 := by
    have h1 : (a * b * a) * (a * b * a) = a * (b * (a * a) * b) * a := by group
    rw [h1, haa]
    simp [hbb, haa]
  have hTinv : (a * b * a)⁻¹ = a * b * a := inv_eq_of_mul_eq_one_right hTT
  have haL : a ∈ L := by
    change φ₁ n0 ∈ L
    rw [← hL']
    exact MonoidHom.mem_range.mpr ⟨n0, rfl⟩
  have hbK : b ∈ K := by
    change φ₂ n0 ∈ K
    rw [← hK']
    exact MonoidHom.mem_range.mpr ⟨n0, rfl⟩
  have hyL : y ∈ L := by
    rw [hy, ← hL']
    exact MonoidHom.mem_range.mpr ⟨lam (0 : Fin (m + 1)) g, rfl⟩
  have hyne : y ≠ 1 := by
    rw [hy]
    intro h
    have h1 : lam (0 : Fin (m + 1)) g = 1 := hφ₁ (by simpa using h)
    have h1' : lam (0 : Fin (m + 1)) g = lam (0 : Fin (m + 1)) 1 := by simpa using h1
    exact hg1 (lam_injective (0 : Fin (m + 1)) h1')
  have hypow : y ^ p = 1 := by
    rw [hy]
    calc (φ₁ (lam (0 : Fin (m + 1)) g)) ^ p
        = φ₁ ((lam (0 : Fin (m + 1)) g) ^ p) := (map_pow φ₁ _ p).symm
      _ = φ₁ ((lam (0 : Fin (m + 1))) (g ^ p)) := by rw [← map_pow (lam (0 : Fin (m + 1))) g p]
      _ = φ₁ ((lam (0 : Fin (m + 1))) 1) := by rw [hg]
      _ = 1 := by rw [map_one, map_one]
  have hordery : orderOf y = p := orderOf_eq_prime hypow hyne
  have hpL : p ∣ Nat.card L := by
    rw [← hordery]
    exact Subgroup.orderOf_dvd_natCard L hyL
  have horderg : orderOf g = p := orderOf_eq_prime hg hg1
  have hpdvd : ¬ p ∣ k := by
    intro hpk
    obtain ⟨c, rfl⟩ := hpk
    have hgk : g ^ (p * c) = 1 := by rw [pow_mul, hg, one_pow]
    exact hx1 (by rw [hx, hgk, map_one, map_one])
  have hcop : Nat.Coprime k p := ((hp.coprime_iff_not_dvd).2 hpdvd).symm
  have hgcd_g : k.gcd (orderOf g) = 1 := by
    rw [horderg]
    exact Nat.coprime_iff_gcd_eq_one.mp hcop
  have hgmem : g ∈ Subgroup.zpowers (g ^ k) := mem_zpowers_pow_iff.mpr hgcd_g
  have haCx : a * x = x * a := by
    have hmem : a ∈ Subgroup.centralizer ({x} : Set G) := hL.1 haL
    rwa [Subgroup.mem_centralizer_singleton_iff] at hmem
  have hxa : a * φ₂ (lam (0 : Fin (m + 1)) g) = φ₂ (lam (0 : Fin (m + 1)) g) * a := by
    have hxmem : φ₂ (lam (0 : Fin (m + 1)) g) ∈ Subgroup.zpowers x := by
      have hψmem : (φ₂.comp (lam (0 : Fin (m + 1)))) g ∈
          Subgroup.zpowers ((φ₂.comp (lam (0 : Fin (m + 1)))) (g ^ k)) := by
        have hmap : (φ₂.comp (lam (0 : Fin (m + 1)))) g ∈
            (Subgroup.zpowers (g ^ k)).map (φ₂.comp (lam (0 : Fin (m + 1)))) :=
          Subgroup.mem_map_of_mem _ hgmem
        rwa [MonoidHom.map_zpowers] at hmap
      rw [hx]
      simpa only [MonoidHom.comp_apply] using hψmem
    have hxC : x ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact haCx.symm
    have hmemC : φ₂ (lam (0 : Fin (m + 1)) g) ∈ Subgroup.centralizer ({a} : Set G) :=
      (Subgroup.zpowers_le.mpr hxC) hxmem
    rw [Subgroup.mem_centralizer_singleton_iff] at hmemC
    exact hmemC.symm
  have haxa : a * x * a = x := by
    calc a * x * a = x * a * a := by rw [haCx]
      _ = x := by rw [mul_assoc, haa, mul_one]
  have hm0 : 0 < m := by omega
  have hm1 : 1 < m := by omega
  let j0 : Fin m := ⟨0, hm0⟩
  let j1 : Fin m := ⟨1, hm1⟩
  have hk0 : (0 : Fin (m + 1)).val + 1 < m + 1 := by simp; omega
  have hswapA : n0 * lam (0 : Fin (m + 1)) (g ^ k) * n0 = lam j0.succ (g ^ k) := by
    have h := weylRep_conj_lam_swap h2 (0 : Fin (m + 1)) hk0 (g ^ k)
    rw [inv_eq_of_mul_eq_one_right (spWeylRep_mul_self (m + 1) h2 0)] at h
    have hidx : (⟨(0 : Fin (m + 1)).val + 1, hk0⟩ : Fin (m + 1)) = j0.succ :=
      Fin.ext (by simp [j0])
    rw [hidx] at h
    exact h
  have hswapB : n0 * lam j0.succ (g ^ k) * n0 = lam (0 : Fin (m + 1)) (g ^ k) := by
    have hconj : n0 * (n0 * lam (0 : Fin (m + 1)) (g ^ k) * n0) * n0 =
        lam (0 : Fin (m + 1)) (g ^ k) := by
      rw [show n0 * (n0 * lam (0 : Fin (m + 1)) (g ^ k) * n0) * n0 =
          (n0 * n0) * lam (0 : Fin (m + 1)) (g ^ k) * (n0 * n0) by group]
      rw [hsp, one_mul, mul_one]
    rw [hswapA] at hconj
    exact hconj
  have hne0 : j1.succ ≠ (0 : Fin (m + 1)) := by
    intro h
    have h2' : (j1.succ : ℕ) = ((0 : Fin (m + 1)) : ℕ) := congrArg Fin.val h
    simp [j1] at h2'
  have hne1 : j1.succ ≠ (⟨(0 : Fin (m + 1)).val + 1, hk0⟩ : Fin (m + 1)) := by
    intro h
    have h2' : (j1.succ : ℕ) =
        ((⟨(0 : Fin (m + 1)).val + 1, hk0⟩ : Fin (m + 1)) : ℕ) := congrArg Fin.val h
    simp [j1] at h2'
  have hswapC : n0 * lam j1.succ g * n0 = lam j1.succ g := by
    have h := weylRep_conj_lam_of_ne h2 (0 : Fin (m + 1)) hk0 hne0 hne1 g
    rw [inv_eq_of_mul_eq_one_right (spWeylRep_mul_self (m + 1) h2 0)] at h
    exact h
  have hbx : b * x * b = φ₁ (lam j0.succ (g ^ k)) := by
    have h1 : b * x * b = φ₂ (n0 * lam (0 : Fin (m + 1)) (g ^ k) * n0) := by
      change φ₂ n0 * x * φ₂ n0 = φ₂ (n0 * lam (0 : Fin (m + 1)) (g ^ k) * n0)
      rw [hx]
      simp only [← map_mul]
    rw [h1, hswapA]
    rw [← spLeviBlock_lam j0 (g ^ k)]
    rw [hβ (lam j0 (g ^ k))]
  have haea_y : a * φ₁ (lam j0.succ (g ^ k)) * a = y ^ k := by
    have h1 : a * φ₁ (lam j0.succ (g ^ k)) * a =
        φ₁ (n0 * lam j0.succ (g ^ k) * n0) := by
      change φ₁ n0 * φ₁ (lam j0.succ (g ^ k)) * φ₁ n0 =
        φ₁ (n0 * lam j0.succ (g ^ k) * n0)
      simp only [← map_mul]
    rw [h1, hswapB, hy, ← map_pow, map_pow]
  have hTxT : (a * b * a) * x * (a * b * a) = y ^ k := by
    have h1 : (a * b * a) * x * (a * b * a) = a * b * x * b * a := by
      rw [show (a * b * a) * x * (a * b * a) = a * b * (a * x * a) * b * a by group, haxa]
    rw [h1]
    have h2' : a * b * x * b * a = a * (b * x * b) * a := by group
    rw [h2', hbx, haea_y]
  have hzw : Subgroup.zpowers ((a * b * a) * x * (a * b * a)⁻¹) = Subgroup.zpowers y := by
    rw [hTinv, hTxT]
    have hgcd_y : k.gcd (orderOf y) = 1 := by
      rw [hordery]
      exact Nat.coprime_iff_gcd_eq_one.mp hcop
    have hymem : y ∈ Subgroup.zpowers (y ^ k) := mem_zpowers_pow_iff.mpr hgcd_y
    exact le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers y k))
      (Subgroup.zpowers_le.mpr hymem)
  have hcenterSp : Subgroup.center (StatedSp (m + 1) F) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have hZ : Subgroup.center K = ⊥ := by
    rw [← hK']
    have hmap := Subgroup.map_center_eq (MonoidHom.ofInjective hφ₂)
    rw [← hmap, hcenterSp, Subgroup.map_bot]
  let e : G := φ₁ (lam j1.succ g)
  have he1 : e ≠ 1 := by
    change φ₁ (lam j1.succ g) ≠ 1
    intro h
    have h1 : lam j1.succ g = 1 := hφ₁ (by simpa using h)
    have h1' : lam j1.succ g = lam j1.succ 1 := by simpa using h1
    exact hg1 (lam_injective j1.succ h1')
  have heβ : φ₁ (lam j1.succ g) = φ₂ (lam j1.succ g) := by
    rw [← spLeviBlock_lam j1 g]
    exact hβ (lam j1 g)
  have heK : e ∈ K := by
    change φ₁ (lam j1.succ g) ∈ K
    rw [heβ, ← hK']
    exact MonoidHom.mem_range.mpr ⟨lam j1.succ g, rfl⟩
  have heLmem : e ∈ L := by
    change φ₁ (lam j1.succ g) ∈ L
    rw [← hL']
    exact MonoidHom.mem_range.mpr ⟨lam j1.succ g, rfl⟩
  have haea : a * e * a = e := by
    have h1 : a * e * a = φ₁ (n0 * lam j1.succ g * n0) := by
      change φ₁ n0 * φ₁ (lam j1.succ g) * φ₁ n0 = φ₁ (n0 * lam j1.succ g * n0)
      simp only [← map_mul]
    rw [h1, hswapC]
  have hbeb : b * e * b = e := by
    change φ₂ n0 * φ₁ (lam j1.succ g) * φ₂ n0 = φ₁ (lam j1.succ g)
    have h1 : φ₂ n0 * φ₁ (lam j1.succ g) * φ₂ n0 = φ₂ (n0 * lam j1.succ g * n0) := by
      rw [heβ]
      simp only [← map_mul]
    rw [h1, hswapC]
    exact heβ.symm
  have hTeT : (a * b * a) * e * (a * b * a) = e := by
    have h1 : (a * b * a) * e * (a * b * a) = a * b * e * b * a := by
      rw [show (a * b * a) * e * (a * b * a) = a * b * (a * e * a) * b * a by group, haea]
    rw [h1]
    have h2' : a * b * e * b * a = a * (b * e * b) * a := by group
    rw [h2', hbeb, haea]
  have heL : e ∈ L.map (MulAut.conj (a * b * a)).toMonoidHom := by
    have hmem : (MulAut.conj (a * b * a)) e ∈ L.map (MulAut.conj (a * b * a)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ heLmem
    have hconj : (MulAut.conj (a * b * a)) e = e := by
      rw [MulAut.conj_apply, hTinv, hTeT]
    rwa [hconj] at hmem
  have hKT : K = L.map (MulAut.conj (a * b * a)).toMonoidHom :=
    spEnd_eq_map_conj_of_component hp (a * b * a) hL hK hzw hpL hZ he1 heK heL
  have hrange : φ₁.range.map (MulAut.conj (a * b * a)).toMonoidHom = φ₂.range := by
    rw [hL', hK', ← hKT]
  have hK_le_y : K ≤ Subgroup.centralizer ({y} : Set G) :=
    ((largeEvenPComponent_iff_lBalance p (Subgroup.centralizer ({y} : Set G)) K).1 hK).1
  have hyK : ∀ w, φ₁ (lam (0 : Fin (m + 1)) g) * φ₂ w =
      φ₂ w * φ₁ (lam (0 : Fin (m + 1)) g) := by
    intro w
    have hwK : φ₂ w ∈ K := by
      rw [← hK']
      exact MonoidHom.mem_range.mpr ⟨w, rfl⟩
    have hcomm : φ₂ w * y = y * φ₂ w := by
      have h := hK_le_y hwK
      rwa [Subgroup.mem_centralizer_singleton_iff] at h
    rw [hy] at hcomm
    exact hcomm.symm
  have htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 :=
    trace_ne_zero_of_pow_eq_one hg1 (hp.odd_of_ne_two hp2) hg
  have hend : (∀ w, (a * b * a) * φ₁ w * (a * b * a)⁻¹ = φ₂ w) ∧
      GGSpEndNode φ₁ (a * b * a) :=
    spEnd_endNode_of_range_conj hm φ₁ φ₂ hφ₁ hφ₂ hβ htr
      (show a * b * a = φ₁ (weylRep (m + 1) F 0) * φ₂ (weylRep (m + 1) F 0) *
          φ₁ (weylRep (m + 1) F 0) from rfl)
      hrange hyK hxa
  exact ⟨a * b * a,
    mul_mem (mul_mem (Subgroup.mem_sup_left haL) (Subgroup.mem_sup_right hbK))
      (Subgroup.mem_sup_left haL), hend.2, hKT⟩

end CFSG.StandardType
