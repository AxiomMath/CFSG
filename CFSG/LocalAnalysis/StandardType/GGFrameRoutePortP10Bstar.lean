module

public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly

private lemma p10bAux_ggGamma_eq_conj {G : Type} [Group G] {Bs K : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ Bs) (hxK : x ∈ K) :
    ggGamma K hN ⟨x, hx⟩ = (MulAut.conj ⟨x, hxK⟩ : MulAut K) := by
  ext l
  rw [MulAut.conj_apply, ggGamma_coe]
  simp

theorem P10b_bstar_decomp {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hZ : Subgroup.center K = ⊥)
    (hinn : ∀ b ∈ Bs, ∃ k ∈ K, ∀ l ∈ K, b * l * b⁻¹ = k * l * k⁻¹)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    ((ggGamma K hN).range.comap (MulAut.conj : K →* MulAut K)).map K.subtype = Bs ⊓ K ∧
      Nat.card ↥(Bs ⊓ K) = 3 ^ (n - 1) ∧
      Subgroup.zpowers z ⊔ (Bs ⊓ K) = Bs ∧ Subgroup.zpowers z ⊓ (Bs ⊓ K) = ⊥ ∧
      ∀ g : K, (∀ e ∈ (Bs ⊓ K).subgroupOf K, g * e = e * g) → g ^ 3 = 1 →
        g ∈ (Bs ⊓ K).subgroupOf K := by
  have hfact3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hCinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
    CFSG.mulAut_conj_injective hZ
  set EK : Subgroup K := (ggGamma K hN).range.comap (MulAut.conj : K →* MulAut K) with hEK
  have hmem : ∀ x : K, x ∈ EK ↔ MulAut.conj x ∈ (ggGamma K hN).range := by
    intro x
    rw [hEK, Subgroup.mem_comap]
  have hzcent : z ∈ Subgroup.centralizer (K : Set G) := by
    have hz' : z ∈ Bs ⊓ Subgroup.centralizer (K : Set G) := by
      rw [hker]
      exact Subgroup.mem_zpowers z
    exact (Subgroup.mem_inf.mp hz').2
  have hA_le : EK.map K.subtype ≤ Bs ⊓ K := by
    rintro x ⟨e, he, rfl⟩
    have he' : MulAut.conj e ∈ (ggGamma K hN).range := (hmem e).mp he
    obtain ⟨b, hb⟩ := he'
    have hb3 : b ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hBs.2 b b.2
    have he3 : e ^ 3 = 1 := by
      apply hCinj
      rw [map_pow, ← hb, ← map_pow, hb3, map_one, map_one]
    have he3' : (e : G) ^ 3 = 1 := by
      simpa using congrArg Subtype.val he3
    refine Subgroup.mem_inf.mpr ⟨hBstar e ?_ he3', e.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hcommγ : ggGamma K hN ⟨b', hb'⟩ * ggGamma K hN b =
        ggGamma K hN b * ggGamma K hN ⟨b', hb'⟩ := by
      rw [← map_mul, ← map_mul, hBs.1.is_comm.comm ⟨b', hb'⟩ b]
    have hkey : MulAut.conj (ggGamma K hN ⟨b', hb'⟩ e) = MulAut.conj e := by
      rw [← CFSG.mulAut_conj_mul_inv (ggGamma K hN ⟨b', hb'⟩) e, ← hb, hcommγ]
      group
    have hfix : ggGamma K hN ⟨b', hb'⟩ e = e := hCinj hkey
    have hcoe : b' * e * b'⁻¹ = (e : G) := by
      rw [← ggGamma_coe K hN ⟨b', hb'⟩ e, hfix]
    calc b' * (e : G) = (b' * e * b'⁻¹) * b' := by group
      _ = (e : G) * b' := by rw [hcoe]
  have hA_ge : Bs ⊓ K ≤ EK.map K.subtype := by
    intro x hx
    obtain ⟨hxB, hxK⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [hmem]
    exact ⟨⟨x, hxB⟩, p10bAux_ggGamma_eq_conj hN hxB hxK⟩
  have hdecomp : ∀ b ∈ Bs, ∃ y ∈ Subgroup.zpowers z, ∃ k ∈ Bs ⊓ K, y * k = b := by
    intro b hb
    obtain ⟨k, hkK, hkact⟩ := hinn b hb
    have hγb : ggGamma K hN ⟨b, hb⟩ = MulAut.conj ⟨k, hkK⟩ := by
      ext l
      rw [MulAut.conj_apply, ggGamma_coe]
      simpa using hkact l l.2
    have hkEK : (⟨k, hkK⟩ : K) ∈ EK := by
      rw [hmem]
      exact ⟨⟨b, hb⟩, hγb⟩
    have hkB : k ∈ Bs := by
      have hmap' : K.subtype (⟨k, hkK⟩ : K) ∈ EK.map K.subtype :=
        Subgroup.mem_map.mpr ⟨⟨k, hkK⟩, hkEK, rfl⟩
      simpa using (Subgroup.mem_inf.mp (hA_le hmap')).1
    have hbkB : b * k⁻¹ ∈ Bs := Bs.mul_mem hb (Bs.inv_mem hkB)
    have hone : ggGamma K hN ⟨b * k⁻¹, hbkB⟩ = 1 := by
      have hmul : ggGamma K hN ⟨b * k⁻¹, hbkB⟩ =
          ggGamma K hN ⟨b, hb⟩ * (ggGamma K hN ⟨k, hkB⟩)⁻¹ := by
        rw [← map_inv, ← map_mul]
        congr 1
      rw [hmul, hγb, p10bAux_ggGamma_eq_conj hN hkB hkK]
      group
    have hcent : (b * k⁻¹ : G) ∈ Subgroup.centralizer (K : Set G) :=
      (ggGamma_eq_one_iff K hN ⟨b * k⁻¹, hbkB⟩).mp hone
    have hzpow : b * k⁻¹ ∈ Subgroup.zpowers z := by
      rw [← hker]
      exact Subgroup.mem_inf.mpr ⟨hbkB, hcent⟩
    exact ⟨b * k⁻¹, hzpow, k, Subgroup.mem_inf.mpr ⟨hkB, hkK⟩, by group⟩
  have hsup : Subgroup.zpowers z ⊔ (Bs ⊓ K) = Bs := by
    refine le_antisymm (sup_le (Subgroup.zpowers_le.mpr hz) inf_le_left) ?_
    intro b hb
    obtain ⟨y, hy, k, hk, rfl⟩ := hdecomp b hb
    exact Subgroup.mul_mem_sup hy hk
  have hdisj : Subgroup.zpowers z ⊓ (Bs ⊓ K) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxz, hxBK⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxB, hxK⟩ := Subgroup.mem_inf.mp hxBK
    have hxC : x ∈ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr hzcent hxz
    have hcenter : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hxC) (g : G) g.2
    rw [hZ, Subgroup.mem_bot] at hcenter
    rw [Subgroup.mem_bot]
    exact Subtype.ext_iff.mp hcenter
  have hprod : Nat.card Bs = 3 * Nat.card ↥(Bs ⊓ K) := by
    have hmemprod : ∀ p : ↥(Subgroup.zpowers z) × ↥(Bs ⊓ K),
        (p.1 : G) * (p.2 : G) ∈ Bs := by
      rintro ⟨a, c⟩
      exact Bs.mul_mem (Subgroup.zpowers_le.mpr hz a.2) (Subgroup.mem_inf.mp c.2).1
    have hbij : Function.Bijective
        (fun p : ↥(Subgroup.zpowers z) × ↥(Bs ⊓ K) =>
          (⟨(p.1 : G) * (p.2 : G), hmemprod p⟩ : Bs)) := by
      constructor
      · rintro ⟨a1, c1⟩ ⟨a2, c2⟩ heq
        have heq' : (a1 : G) * (c1 : G) = (a2 : G) * (c2 : G) := congrArg Subtype.val heq
        have h1 : (a2 : G)⁻¹ * (a1 : G) = (c2 : G) * (c1 : G)⁻¹ := by
          calc (a2 : G)⁻¹ * (a1 : G)
              = (a2 : G)⁻¹ * ((a1 : G) * (c1 : G)) * (c1 : G)⁻¹ := by group
            _ = (a2 : G)⁻¹ * ((a2 : G) * (c2 : G)) * (c1 : G)⁻¹ := by rw [heq']
            _ = (c2 : G) * (c1 : G)⁻¹ := by group
        have hin : (a2 : G)⁻¹ * (a1 : G) ∈ Subgroup.zpowers z ⊓ (Bs ⊓ K) := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · exact (Subgroup.zpowers z).mul_mem ((Subgroup.zpowers z).inv_mem a2.2) a1.2
          · rw [h1]
            exact (Bs ⊓ K).mul_mem c2.2 ((Bs ⊓ K).inv_mem c1.2)
        rw [hdisj, Subgroup.mem_bot] at hin
        have ha : a1 = a2 := by
          apply Subtype.ext
          calc (a1 : G) = (a2 : G) * ((a2 : G)⁻¹ * (a1 : G)) := by group
            _ = (a2 : G) := by rw [hin]; group
        have hc : c1 = c2 := by
          have h2 : (c2 : G) * (c1 : G)⁻¹ = 1 := by rw [← h1]; exact hin
          have hc' : (c2 : G) = (c1 : G) := by
            calc (c2 : G) = (c2 : G) * (c1 : G)⁻¹ * (c1 : G) := by group
              _ = (c1 : G) := by rw [h2]; group
          exact Subtype.ext hc'.symm
        exact Prod.ext ha hc
      · intro b
        obtain ⟨y, hy, k, hk, hyk⟩ := hdecomp (b : G) b.2
        exact ⟨(⟨y, hy⟩, ⟨k, hk⟩), Subtype.ext hyk⟩
    have h := Nat.card_eq_of_bijective _ hbij
    rw [Nat.card_prod, Nat.card_zpowers, orderOf_eq_prime (hBs.2 z hz) hz1] at h
    exact h.symm
  refine ⟨?_, ?_, hsup, hdisj, ?_⟩
  · rw [le_antisymm hA_le hA_ge]
  · have h := hprod
    rw [hcard] at h
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n
      rw [pow_zero] at hcard
      rw [Subgroup.card_eq_one] at hcard
      exact absurd (Subgroup.mem_bot.mp (hcard ▸ hz)) hz1
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      rw [pow_succ] at h
      have h' : 3 * 3 ^ m = 3 * Nat.card ↥(Bs ⊓ K) := by
        rw [mul_comm 3 (3 ^ m)]
        exact h
      have h2 : 3 ^ m = Nat.card ↥(Bs ⊓ K) := Nat.mul_left_cancel (by norm_num) h'
      rw [Nat.succ_sub_one]
      exact h2.symm
  · intro g hgc hg3
    have hBsle : Bs ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
      rw [← hsup]
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxC : x ∈ Subgroup.centralizer (K : Set G) :=
          Subgroup.zpowers_le.mpr hzcent hx
        exact ((Subgroup.mem_centralizer_iff.mp hxC) (g : G) g.2).symm
      · intro x hx
        obtain ⟨hxB, hxK⟩ := Subgroup.mem_inf.mp hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hxsub : (⟨x, hxK⟩ : K) ∈ (Bs ⊓ K).subgroupOf K := by
          rw [Subgroup.mem_subgroupOf]
          exact Subgroup.mem_inf.mpr ⟨hxB, hxK⟩
        exact (congrArg Subtype.val (hgc ⟨x, hxK⟩ hxsub)).symm
    have hmemC : (g : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := hBsle hb
      rwa [Subgroup.mem_centralizer_singleton_iff] at h
    have hg3' : (g : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hg3
    have hgBs : (g : G) ∈ Bs := hBstar (g : G) hmemC hg3'
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hgBs, g.2⟩

end CFSG.StandardType.FrameRoute
