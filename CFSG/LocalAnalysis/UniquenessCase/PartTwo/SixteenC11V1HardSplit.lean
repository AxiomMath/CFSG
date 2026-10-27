module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardSummand

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem s16c11_v1_two_summand_cover {M W' : Type} [CommGroup M] [CommGroup W']
    {A : Subgroup (MulAut M)} {B : Subgroup (MulAut W')} (e : ↥B →* ↥A)
    (he : Function.Surjective e) (κ : M × M →* W') (hκ : Function.Surjective κ)
    (hequiv : ∀ (b : ↥B) (x : M × M),
      κ (((e b : ↥A) : MulAut M) x.1, ((e b : ↥A) : MulAut M) x.2) =
        (b : MulAut W') (κ x))
    (hker : ∀ x : M × M, κ x = 1 → x.1 ∈ fixV A ∧ x.2 ∈ fixV A) (hfix : fixV B = ⊥)
    {I₀ I₁ : Subgroup W'} (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤)
    (hirr₀ : IsIrrOn B I₀ ⊥) (hirr₁ : IsIrrOn B I₁ ⊥) {D₀ D₁ : FFModel}
    (hR₀ : D₀.Realizes B I₀ ⊥) (hR₁ : D₁.Realizes B I₁ ⊥) :
    D₀.Realizes A ⊤ (fixV A) ∨ D₁.Realizes A ⊤ (fixV A) := by
  let N : Subgroup W' := (κ.comp (MonoidHom.inl M M)).range
  let N' : Subgroup W' := (κ.comp (MonoidHom.inr M M)).range
  have hNmem : ∀ m : M, κ (m, 1) ∈ N := fun m => MonoidHom.mem_range.mpr ⟨m, rfl⟩
  have hN'mem : ∀ m : M, κ (1, m) ∈ N' := fun m => MonoidHom.mem_range.mpr ⟨m, rfl⟩
  have hNstable : StableUnder B N := by
    intro b hb n hn
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hn
    have hm1 : κ (m, 1) = n := by simpa using hm
    rw [← hm1]
    refine MonoidHom.mem_range.mpr ⟨((e ⟨b, hb⟩ : ↥A) : MulAut M) m, ?_⟩
    have h := hequiv ⟨b, hb⟩ (m, 1)
    simpa using h
  have hN'stable : StableUnder B N' := by
    intro b hb n hn
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hn
    have hm1 : κ (1, m) = n := by simpa using hm
    rw [← hm1]
    refine MonoidHom.mem_range.mpr ⟨((e ⟨b, hb⟩ : ↥A) : MulAut M) m, ?_⟩
    have h := hequiv ⟨b, hb⟩ (1, m)
    simpa using h
  have hNsup : N ⊔ N' = ⊤ := by
    rw [eq_top_iff]
    rintro w -
    obtain ⟨x, rfl⟩ := hκ w
    have hsplit : x = (x.1, 1) * (1, x.2) := by ext <;> simp
    rw [hsplit, map_mul]
    exact Subgroup.mul_mem_sup (hNmem x.1) (hN'mem x.2)
  have hfst : ∀ m ∈ fixV A, κ (m, 1) = 1 := by
    intro m hm
    have hmem : κ (m, 1) ∈ fixV B := by
      rw [mem_fixV]
      intro b hb
      have h := hequiv ⟨b, hb⟩ (m, 1)
      rw [← h]
      have hbm : ((e ⟨b, hb⟩ : ↥A) : MulAut M) m = m := hm _ (e ⟨b, hb⟩).2
      rw [hbm, map_one]
    rw [hfix] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hsnd : ∀ m ∈ fixV A, κ (1, m) = 1 := by
    intro m hm
    have hmem : κ (1, m) ∈ fixV B := by
      rw [mem_fixV]
      intro b hb
      have h := hequiv ⟨b, hb⟩ (1, m)
      rw [← h]
      have hbm : ((e ⟨b, hb⟩ : ↥A) : MulAut M) m = m := hm _ (e ⟨b, hb⟩).2
      rw [map_one, hbm]
    rw [hfix] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hNinf : N ⊓ N' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwN, hwN'⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hwN
    obtain ⟨m', hm'⟩ := MonoidHom.mem_range.mp hwN'
    have hm1 : κ (m, 1) = w := by simpa using hm
    have hm2 : κ (1, m') = w := by simpa using hm'
    have hmul : κ (m, m'⁻¹) = 1 := by
      have hsplit : (m, m'⁻¹) = (m, 1) * (1, m'⁻¹) := by ext <;> simp
      rw [hsplit, map_mul]
      have hinv : κ (1, m'⁻¹) = w⁻¹ := by
        have hsplit' : (1, m'⁻¹) = ((1, m') : M × M)⁻¹ := by ext <;> simp
        rw [hsplit', map_inv, hm2]
      rw [hm1, hinv, mul_inv_cancel]
    exact Subgroup.mem_bot.mpr (by
      have hmA := (hker (m, m'⁻¹) hmul).1
      rw [← hm1, hfst m hmA])
  have hN0 : N ≠ ⊥ := by
    intro hNbot
    have hall : ∀ m : M, κ (m, 1) = 1 := by
      intro m
      have h : κ (m, 1) ∈ N := hNmem m
      rw [hNbot] at h
      exact Subgroup.mem_bot.mp h
    have hallfix : ∀ m : M, m ∈ fixV A := fun m => (hker (m, 1) (hall m)).1
    have hN'bot : N' = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hw
      have hm1 : κ (1, m) = w := by simpa using hm
      exact Subgroup.mem_bot.mpr (by rw [← hm1, hsnd m (hallfix m)])
    have htopbot : (⊤ : Subgroup W') = ⊥ := by
      rw [← hNsup, hNbot, hN'bot]
      simp
    have hIbot : I₀ = ⊥ := le_bot_iff.mp (htopbot ▸ le_top)
    exact (ne_of_gt hirr₀.1) hIbot
  have hN'0 : N' ≠ ⊥ := by
    intro hN'bot
    have hall : ∀ m : M, κ (1, m) = 1 := by
      intro m
      have h : κ (1, m) ∈ N' := hN'mem m
      rw [hN'bot] at h
      exact Subgroup.mem_bot.mp h
    have hallfix : ∀ m : M, m ∈ fixV A := fun m => (hker (1, m) (hall m)).2
    have hNbot : N = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hw
      have hm1 : κ (m, 1) = w := by simpa using hm
      exact Subgroup.mem_bot.mpr (by rw [← hm1, hfst m (hallfix m)])
    have htopbot : (⊤ : Subgroup W') = ⊥ := by
      rw [← hNsup, hNbot, hN'bot]
      simp
    have hIbot : I₀ = ⊥ := le_bot_iff.mp (htopbot ▸ le_top)
    exact (ne_of_gt hirr₀.1) hIbot
  obtain ⟨I, s, hI, hsbij, hsequiv⟩ :=
    s16c11_v1_exists_iso_summand (B := B) hinf hsup hirr₀ hirr₁ hNstable hN'stable
      hNinf hNsup hN0 hN'0
  rcases hI with hI₀ | hI₁
  · have hR₀' : D₀.Realizes B I ⊥ := hI₀.symm ▸ hR₀
    have hcomp : D₀.Realizes B N ((s.ker).map N.subtype) :=
      s16c11_v1_realizes_comp (W := W') (W' := W') (A := B) (B := B)
        (MonoidHom.id ↥B) (fun b => ⟨b, rfl⟩) (U := N) hNstable s hsbij.2
        (fun b u => hsequiv (b : MulAut W') b.2 u) hR₀'
    have hcomp' : D₀.Realizes B N ⊥ := by
      have hkerbot : s.ker = ⊥ := (MonoidHom.ker_eq_bot_iff s).mpr hsbij.1
      simpa [hkerbot] using hcomp
    let f : M →* ↥N := (κ.comp (MonoidHom.inl M M)).codRestrict N hNmem
    let s₂ : ↥(⊤ : Subgroup M) →* ↥N := f.comp (⊤ : Subgroup M).subtype
    have hs₂coe : ∀ u : ↥(⊤ : Subgroup M), ((s₂ u : ↥N) : W') = κ ((u : M), 1) :=
      fun u => rfl
    have hs₂surj : Function.Surjective s₂ := by
      intro n
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp n.2
      have hm1 : κ (m, 1) = (n : W') := by simpa using hm
      exact ⟨⟨m, Subgroup.mem_top m⟩, Subtype.ext (by rw [hs₂coe, hm1])⟩
    have hequiv₂ : ∀ (b : ↥B) (u : ↥(⊤ : Subgroup M)),
        ((s₂ ⟨((e b : ↥A) : MulAut M) (u : M), Subgroup.mem_top _⟩ : ↥N) : W') =
          (b : MulAut W') ((s₂ u : ↥N) : W') := by
      intro b u
      rw [hs₂coe, hs₂coe]
      have h := hequiv b ((u : M), 1)
      simpa using h
    have hcomp₂ : D₀.Realizes A ⊤ ((s₂.ker).map (⊤ : Subgroup M).subtype) :=
      s16c11_v1_realizes_comp (W := M) (W' := W') (A := A) (B := B) e he (U := ⊤)
        (fun _ _ _ _ => Subgroup.mem_top _) (I := N) s₂ hs₂surj hequiv₂ hcomp'
    have hker_map : (s₂.ker).map (⊤ : Subgroup M).subtype = fixV A := by
      ext m
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨u, hu, rfl⟩
        have h1 : s₂ u = 1 := MonoidHom.mem_ker.mp hu
        have hk : κ ((u : M), 1) = 1 := by rw [← hs₂coe u, h1]; rfl
        exact (hker ((u : M), 1) hk).1
      · intro hm
        refine ⟨⟨m, Subgroup.mem_top m⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
        apply Subtype.ext
        rw [hs₂coe, hfst m hm]
        rfl
    exact Or.inl (hker_map ▸ hcomp₂)
  · have hR₁' : D₁.Realizes B I ⊥ := hI₁.symm ▸ hR₁
    have hcomp : D₁.Realizes B N ((s.ker).map N.subtype) :=
      s16c11_v1_realizes_comp (W := W') (W' := W') (A := B) (B := B)
        (MonoidHom.id ↥B) (fun b => ⟨b, rfl⟩) (U := N) hNstable s hsbij.2
        (fun b u => hsequiv (b : MulAut W') b.2 u) hR₁'
    have hcomp' : D₁.Realizes B N ⊥ := by
      have hkerbot : s.ker = ⊥ := (MonoidHom.ker_eq_bot_iff s).mpr hsbij.1
      simpa [hkerbot] using hcomp
    let f : M →* ↥N := (κ.comp (MonoidHom.inl M M)).codRestrict N hNmem
    let s₂ : ↥(⊤ : Subgroup M) →* ↥N := f.comp (⊤ : Subgroup M).subtype
    have hs₂coe : ∀ u : ↥(⊤ : Subgroup M), ((s₂ u : ↥N) : W') = κ ((u : M), 1) :=
      fun u => rfl
    have hs₂surj : Function.Surjective s₂ := by
      intro n
      obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp n.2
      have hm1 : κ (m, 1) = (n : W') := by simpa using hm
      exact ⟨⟨m, Subgroup.mem_top m⟩, Subtype.ext (by rw [hs₂coe, hm1])⟩
    have hequiv₂ : ∀ (b : ↥B) (u : ↥(⊤ : Subgroup M)),
        ((s₂ ⟨((e b : ↥A) : MulAut M) (u : M), Subgroup.mem_top _⟩ : ↥N) : W') =
          (b : MulAut W') ((s₂ u : ↥N) : W') := by
      intro b u
      rw [hs₂coe, hs₂coe]
      have h := hequiv b ((u : M), 1)
      simpa using h
    have hcomp₂ : D₁.Realizes A ⊤ ((s₂.ker).map (⊤ : Subgroup M).subtype) :=
      s16c11_v1_realizes_comp (W := M) (W' := W') (A := A) (B := B) e he (U := ⊤)
        (fun _ _ _ _ => Subgroup.mem_top _) (I := N) s₂ hs₂surj hequiv₂ hcomp'
    have hker_map : (s₂.ker).map (⊤ : Subgroup M).subtype = fixV A := by
      ext m
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨u, hu, rfl⟩
        have h1 : s₂ u = 1 := MonoidHom.mem_ker.mp hu
        have hk : κ ((u : M), 1) = 1 := by rw [← hs₂coe u, h1]; rfl
        exact (hker ((u : M), 1) hk).1
      · intro hm
        refine ⟨⟨m, Subgroup.mem_top m⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
        apply Subtype.ext
        rw [hs₂coe, hfst m hm]
        rfl
    exact Or.inr (hker_map ▸ hcomp₂)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
