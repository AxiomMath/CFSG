module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CenterThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08x1p_norm {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hZ : ∀ b ∈ Bs, ∀ z ∈ Subgroup.center ↥L, (b : G) * ((z : ↥L) : G) = ((z : ↥L) : G) * b)
    (hP : ∀ b ∈ Bs, (∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set G), (b : G) = l * c) →
      (b : G) ∈ (Bs ⊓ L) ⊔ Subgroup.zpowers x)
    (l : ↥L) (hl : (MulAut.conj l : MulAut ↥L) ∈
      Subgroup.normalizer (((ggGamma L hBsN).range : Subgroup (MulAut ↥L)) : Set (MulAut ↥L))) :
    (l : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  obtain ⟨hp, hBs, hxB, hLx, h4⟩ := hS.1.1.tableB_facts
  have hx3 : x ^ 3 = 1 := hBs.2 x hxB
  have hxcomm : ∀ u ∈ L, x * u = u * x := fun u hu =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLx hu)).symm
  let T : Subgroup G :=
    { carrier := {g : G | ∃ l ∈ L, ∃ k : ℤ, g = l * x ^ k}
      one_mem' := ⟨1, L.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro g h ⟨l₁, hl₁, k₁, rfl⟩ ⟨l₂, hl₂, k₂, rfl⟩
        refine ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, k₁ + k₂, ?_⟩
        have hxcl : Commute x l₂ := hxcomm l₂ hl₂
        calc (l₁ * x ^ k₁) * (l₂ * x ^ k₂)
            = l₁ * (x ^ k₁ * l₂) * x ^ k₂ := by group
          _ = l₁ * (l₂ * x ^ k₁) * x ^ k₂ := by rw [(hxcl.zpow_left k₁).eq]
          _ = (l₁ * l₂) * x ^ (k₁ + k₂) := by rw [zpow_add]; group
      inv_mem' := by
        rintro g ⟨l, hl, k, rfl⟩
        refine ⟨l⁻¹, L.inv_mem hl, -k, ?_⟩
        rw [mul_inv_rev, ← zpow_neg]
        exact ((show Commute x l from hxcomm l hl).zpow_left (-k)).inv_right.eq }
  have hLT : L ≤ T := fun g hg => ⟨g, hg, 0, by simp⟩
  have hzT : Subgroup.zpowers x ≤ T := by
    intro g hg
    rw [Subgroup.mem_zpowers_iff] at hg
    obtain ⟨k, rfl⟩ := hg
    exact ⟨1, L.one_mem, k, by simp⟩
  have hsup : (Bs ⊓ L) ⊔ Subgroup.zpowers x ≤ T :=
    sup_le (le_trans inf_le_right hLT) hzT
  set A : Subgroup (MulAut ↥L) := (ggGamma L hBsN).range with hA
  have key : ∀ (l' : ↥L), (MulAut.conj l' : MulAut ↥L) ∈
      Subgroup.normalizer (A : Set (MulAut ↥L)) →
      ∀ b ∈ Bs, (l' : G) * b * (l' : G)⁻¹ ∈ Bs := by
    intro l' hl' b hb
    let bB : ↥Bs := ⟨b, hb⟩
    have hγb : ggGamma L hBsN bB ∈ A := ⟨bB, rfl⟩
    have hconj : (MulAut.conj l' : MulAut ↥L) * ggGamma L hBsN bB *
        (MulAut.conj l')⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp hl' (ggGamma L hBsN bB)).mp hγb
    rcases hconj with ⟨b', hb'⟩
    let c : G := (l' : G) * b * (l' : G)⁻¹
    let d : G := (b' : G)⁻¹ * c
    let u₀ : G := (b : G)⁻¹ * (l' : G) * b * (l' : G)⁻¹
    have hd_comm : ∀ u : ↥L, d * (u : G) = (u : G) * d := by
      intro u
      have h := congrArg (fun φ : MulAut ↥L => ((φ u : ↥L) : G)) hb'
      simp only [ggGamma_coe, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply,
        Subgroup.coe_mul, Subgroup.coe_inv] at h
      have h1 : (b' : G) * (u : G) * (b' : G)⁻¹ = c * (u : G) * c⁻¹ := by
        rw [h]; dsimp [c, bB]; group
      calc d * (u : G) = (b' : G)⁻¹ * (c * (u : G) * c⁻¹) * c := by dsimp [d]; group
        _ = (b' : G)⁻¹ * ((b' : G) * (u : G) * (b' : G)⁻¹) * c := by rw [← h1]
        _ = (u : G) * d := by dsimp [d]; group
    have hdC : d ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (hd_comm ⟨m, hm⟩).symm
    have hu₀L : u₀ ∈ L := by
      have hblb : (b : G)⁻¹ * (l' : G) * b ∈ L :=
        (Subgroup.mem_normalizer_iff''.mp (hBsN hb) (l' : G)).mp l'.2
      exact L.mul_mem hblb (L.inv_mem l'.2)
    let b'' : G := (b' : G)⁻¹ * b
    have hb'' : b'' ∈ Bs := Bs.mul_mem (Bs.inv_mem b'.2) hb
    have hd_eq : d = b'' * u₀ := by dsimp [d, b'', u₀, c]; group
    have hb''_mem : b'' ∈ (Bs ⊓ L) ⊔ Subgroup.zpowers x := by
      refine hP b'' hb'' ⟨u₀⁻¹, L.inv_mem hu₀L, d, hdC, ?_⟩
      have hdu : Commute d u₀ := ((Subgroup.mem_centralizer_iff.mp hdC) u₀ hu₀L).symm
      have hdu' : Commute d u₀⁻¹ := hdu.inv_right
      have h1 : b'' = d * u₀⁻¹ := by rw [hd_eq]; group
      rw [h1, hdu'.eq]
    obtain ⟨l₂, hl₂, k, hk⟩ := hsup hb''_mem
    let z : G := l₂ * u₀
    have hzL : z ∈ L := L.mul_mem hl₂ hu₀L
    have hdz : d = z * x ^ k := by
      have hxku : x ^ k * u₀ = u₀ * x ^ k :=
        ((show Commute x u₀ from hxcomm u₀ hu₀L).zpow_left k).eq
      dsimp [z]
      rw [hd_eq, hk]
      calc (l₂ * x ^ k) * u₀ = l₂ * (x ^ k * u₀) := mul_assoc l₂ (x ^ k) u₀
        _ = l₂ * (u₀ * x ^ k) := by rw [hxku]
        _ = (l₂ * u₀) * x ^ k := (mul_assoc l₂ u₀ (x ^ k)).symm
    have hzC : z ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hdm : Commute m d := (Subgroup.mem_centralizer_iff.mp hdC) m hm
      have hxm : Commute m (x ^ (-k)) :=
        ((show Commute x m from hxcomm m hm).zpow_left (-k)).symm
      have hz_eq : z = d * x ^ (-k) := by rw [hdz]; group
      rw [hz_eq]
      exact (hdm.mul_right hxm).eq
    have hzcen : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (Subgroup.mem_centralizer_iff.mp hzC) (y : G) y.2
    have hb'z : Commute (b' : G) z := hZ (b' : G) b'.2 ⟨z, hzL⟩ hzcen
    have hb'x : Commute (b' : G) x := by
      haveI : IsMulCommutative ↥Bs := hBs.1
      show (b' : G) * x = x * (b' : G)
      exact congrArg Subtype.val (mul_comm' b' (⟨x, hxB⟩ : ↥Bs))
    have hb'd : Commute (b' : G) d := by
      rw [hdz]
      exact hb'z.mul_right (hb'x.zpow_right k)
    have hd3 : d ^ (3 : ℕ) = 1 := by
      have h1 : ((b' : G) * d) ^ (3 : ℕ) = (b' : G) ^ (3 : ℕ) * d ^ (3 : ℕ) :=
        hb'd.mul_pow 3
      have h2 : ((b' : G) * d) ^ (3 : ℕ) = 1 := by
        have hc_eq : (b' : G) * d = (l' : G) * b * (l' : G)⁻¹ := by dsimp [d, c]; group
        have hconj3 : ((l' : G) * b * (l' : G)⁻¹) ^ (3 : ℕ) =
            (l' : G) * b ^ (3 : ℕ) * (l' : G)⁻¹ := by
          rw [← MulAut.conj_apply (l' : G) b, ← map_pow (MulAut.conj (l' : G)) b 3,
            MulAut.conj_apply]
        rw [hc_eq, hconj3, hBs.2 b hb]
        group
      have hb'3 : (b' : G) ^ (3 : ℕ) = 1 := hBs.2 (b' : G) b'.2
      rw [h2, hb'3, one_mul] at h1
      exact h1.symm
    have hzx : Commute z x := Subgroup.mem_centralizer_singleton_iff.mp (hLx hzL)
    have hz3 : z ^ (3 : ℕ) = 1 := by
      have hcomm : Commute z (x ^ k) := hzx.zpow_right k
      have hw3 : (x ^ k) ^ (3 : ℕ) = 1 := by
        have e1 : (x ^ k) ^ (3 : ℕ) = (x ^ k) ^ ((3 : ℕ) : ℤ) :=
          (zpow_natCast (x ^ k) 3).symm
        have e2 : (x ^ k) ^ ((3 : ℕ) : ℤ) = x ^ (k * ((3 : ℕ) : ℤ)) :=
          (zpow_mul x k ((3 : ℕ) : ℤ)).symm
        have e3 : x ^ (k * ((3 : ℕ) : ℤ)) = x ^ (((3 : ℕ) : ℤ) * k) :=
          congrArg (fun t => x ^ t) (Int.mul_comm k ((3 : ℕ) : ℤ))
        have e4 : x ^ (((3 : ℕ) : ℤ) * k) = (x ^ ((3 : ℕ) : ℤ)) ^ k :=
          zpow_mul x ((3 : ℕ) : ℤ) k
        have e5 : (x ^ ((3 : ℕ) : ℤ)) ^ k = (x ^ 3) ^ k := by rw [zpow_natCast]
        rw [e1, e2, e3, e4, e5, hx3, one_zpow]
      have hdz3 : d ^ (3 : ℕ) = z ^ (3 : ℕ) * (x ^ k) ^ (3 : ℕ) := by
        rw [hdz]; exact hcomm.mul_pow 3
      rw [hw3, mul_one] at hdz3
      rw [← hdz3, hd3]
    have h3 : (⟨z, hzL⟩ : ↥L) ^ (3 : ℕ) = 1 := by
      apply Subtype.ext
      simpa using hz3
    have hzmem : z ∈ Subgroup.zpowers x := by
      have := ggQ2s08_center_three_mem hS ⟨z, hzL⟩ hzcen h3
      simpa using this
    have hdmem : d ∈ Subgroup.zpowers x := by
      rw [hdz]
      exact Subgroup.mul_mem _ hzmem (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    have hdBs : d ∈ Bs := (Subgroup.zpowers_le.mpr hxB) hdmem
    have hc_eq : c = (b' : G) * d := by dsimp [c, d]; group
    have hcBs : c ∈ Bs := by rw [hc_eq]; exact Bs.mul_mem b'.2 hdBs
    show c ∈ Bs
    exact hcBs
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact key l hl b hb
  · intro hb
    have hl_inv : MulAut.conj (l⁻¹) ∈ Subgroup.normalizer (A : Set (MulAut ↥L)) := by
      rw [map_inv]
      exact Subgroup.inv_mem _ hl
    have h := key l⁻¹ hl_inv ((l : G) * b * (l : G)⁻¹) hb
    rw [Subgroup.coe_inv] at h
    convert h using 1 <;> group

end CFSG.StandardType

end
