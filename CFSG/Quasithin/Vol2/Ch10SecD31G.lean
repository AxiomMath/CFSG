module

public import CFSG.Quasithin.Vol2.Ch10SecD211A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

@[expose] def L3.stabVec (c : CFSG.Quasithin.L3.Vec) : Subgroup CFSG.Quasithin.L3.Γ where
  carrier := {γ | CFSG.Quasithin.L3.act γ c = c}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [CFSG.Quasithin.L3.act_mul, hb, ha]
  one_mem' := CFSG.Quasithin.L3.act_one c
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    exact CFSG.Quasithin.L3.act_inv_act a c

theorem not_isMaxSubgroupIn_of_le_T (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    {N : Subgroup G} (hNT : N ≤ T) (hNL : N ≤ L) : ¬ IsMaxSubgroupIn L N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨-, hmax⟩
  obtain ⟨-, hcomm, hnat⟩ := h3
  obtain ⟨D⟩ := hnat.toL3Coord
  have hLN : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) := L_le_normalizer_V1
  let f : ↥L →* ↥(autOn L (fsuUL T L I)) :=
    ((conjAct (fsuUL T L I)).comp (Subgroup.inclusion hLN)).codRestrict (autOn L (fsuUL T L I))
      (fun l => ⟨⟨l, hLN l.2⟩, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩)
  have hfsurj : Function.Surjective f := by
    rintro ⟨_, ⟨⟨l, hlN⟩, hl, rfl⟩⟩
    exact ⟨⟨l, Subgroup.mem_subgroupOf.mp hl⟩, rfl⟩
  let e : CFSG.Quasithin.L3.Γ ≃* ↥(autOn L (fsuUL T L I)) :=
    MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩
  let lam : ↥L →* CFSG.Quasithin.L3.Γ := e.symm.toMonoidHom.comp f
  have hlam_surj : Function.Surjective lam := e.symm.surjective.comp hfsurj
  have hrho : ∀ l : ↥L, D.rho (lam l) = conjAct (fsuUL T L I) ⟨l, hLN l.2⟩ := by
    intro l
    have h1 : D.π (lam l) = f l := e.apply_symm_apply (f l)
    exact congrArg Subtype.val h1
  have hS : IsSylowTwoOf (T ⊓ L) L := SecA.isSylowTwoOf_inf h.fsu.maximal.1
  have hP8 : Nat.card (autOn (T ⊓ L) (fsuUL T L I)) = 8 := D.card_sylow (isSylowTwoOf_autOn hS hLN)
  set P := (autOn (T ⊓ L) (fsuUL T L I)).comap D.rho with hP
  have hrange : autOn (T ⊓ L) (fsuUL T L I) ≤ D.rho.range := fun σ hσ => by
    obtain ⟨γ, hγ⟩ := D.exists_rho (A4.autOn_mono hS.1 hσ)
    exact ⟨γ, hγ⟩
  have hPc : Nat.card P = 8 := by
    rw [← hP8, ← Subgroup.map_comap_eq_self hrange,
      Subgroup.card_map_of_injective D.rho_injective]
  have hfix := L3.card_fix_of_card_eq_eight hPc
  obtain ⟨c, hc0, hcP⟩ : ∃ c : CFSG.Quasithin.L3.Vec, c ≠ 0 ∧
      ∀ γ ∈ P, CFSG.Quasithin.L3.act γ c = c := by
    have : Nontrivial {v : CFSG.Quasithin.L3.Vec // ∀ g ∈ P, CFSG.Quasithin.L3.act g v = v} :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hfix]; norm_num)
    obtain ⟨⟨c, hc⟩, hc0⟩ := exists_ne (⟨0, fun g _ => CFSG.Quasithin.L3.act_zero g⟩ :
      {v : CFSG.Quasithin.L3.Vec // ∀ g ∈ P, CFSG.Quasithin.L3.act g v = v})
    exact ⟨c, fun h0 => hc0 (Subtype.ext h0), hc⟩
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hPc]; norm_num)
  have hNP : ∀ (n : G) (hn : n ∈ N), lam ⟨n, hNL hn⟩ ∈ P := by
    intro n hn
    show D.rho (lam ⟨n, hNL hn⟩) ∈ autOn (T ⊓ L) (fsuUL T L I)
    rw [hrho]
    exact ⟨⟨n, hLN (hNL hn)⟩, Subgroup.mem_subgroupOf.mpr ⟨hNT hn, hNL hn⟩, rfl⟩
  set St : Subgroup G := ((L3.stabVec c).comap lam).map L.subtype with hSt
  have hNSt : N ≤ St := fun n hn =>
    ⟨⟨n, hNL hn⟩, hcP _ (hNP n hn), rfl⟩
  have hStL : St ≤ L := Subgroup.map_subtype_le _
  obtain ⟨γ3, hγ3c, hγ33, hγ31⟩ := L3.exists_order_three_fix c hc0
  obtain ⟨l3, hl3⟩ := hlam_surj γ3
  have hl3St : (l3 : G) ∈ St := ⟨l3, by show L3.act (lam l3) c = c; rw [hl3]; exact hγ3c, rfl⟩
  have hl3N : (l3 : G) ∉ N := by
    intro hl3N
    have hmem : lam ⟨(l3 : G), hNL hl3N⟩ ∈ P := hNP _ hl3N
    have he : (⟨(l3 : G), hNL hl3N⟩ : ↥L) = l3 := rfl
    rw [he, hl3] at hmem
    obtain ⟨k, hk⟩ := hP2 ⟨γ3, hmem⟩
    have hk' : γ3 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : orderOf γ3 ∣ 3 := orderOf_dvd_of_pow_eq_one hγ33
    have h2 : orderOf γ3 ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h3' : orderOf γ3 ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at h3'
    exact hγ31 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3'))
  have hNlt : N < St := lt_of_le_of_ne hNSt fun heq => hl3N (heq ▸ hl3St)
  have hStEq := hmax St hNlt hStL
  obtain ⟨γ', hγ'⟩ := CFSG.Quasithin.L3.act_nofix c hc0
  obtain ⟨l', hl'⟩ := hlam_surj γ'
  have hl'St : (l' : G) ∈ St := by
    rw [hStEq]
    exact l'.2
  obtain ⟨l'', hl'', hl''e⟩ := hl'St
  have he : l'' = l' := Subtype.ext hl''e
  rw [he] at hl''
  apply hγ'
  have : L3.act (lam l') c = c := hl''
  rwa [hl'] at this

end CFSG.Quasithin.Vol2.Ch10.SecD
