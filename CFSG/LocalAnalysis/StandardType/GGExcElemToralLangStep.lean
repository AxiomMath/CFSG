module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ToralCentralizerGenerated

public section

namespace CFSG.StandardType.ExcElemToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg


theorem exists_frobenius_fixed_conj_of_family {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] {e : ℕ} (he : 1 ≤ e)
    {ι : Type} (a : ι → Fin τ.rank → Lˣ) (ha : ∀ i j, a i j ^ ℓ ^ e = a i j)
    (hcent : familyCentralizer τ L a = familyGroup (K := L) a)
    {g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hx : ∀ i, entrywiseFrobGL τ L ℓ e (g⁻¹ * rootDiagUnit τ (a i) * g) =
      g⁻¹ * rootDiagUnit τ (a i) * g) :
    ∃ h ∈ adjointGroup τ L, entrywiseFrobGL τ L ℓ e h = h ∧
      ∀ i, h⁻¹ * rootDiagUnit τ (a i) * h = g⁻¹ * rootDiagUnit τ (a i) * g := by
  let F := entrywiseFrobGL τ L ℓ e
  let m : ModGL τ L := F g * g⁻¹
  have hFd : ∀ i, F (rootDiagUnit τ (a i)) = rootDiagUnit τ (a i) := by
    intro i
    change entrywiseFrobGL τ L ℓ e (rootDiagUnit τ (a i)) = _
    rw [entrywiseFrobGL_rootDiagUnit_eq_pow]
    exact congrArg (rootDiagUnit τ) (funext (ha i))
  have hmG : m ∈ adjointGroup τ L :=
    mul_mem (entrywiseFrobGL_mem ℓ e hg) (inv_mem hg)
  have hconj : ∀ i, (F g)⁻¹ * rootDiagUnit τ (a i) * F g =
      g⁻¹ * rootDiagUnit τ (a i) * g := by
    intro i
    have h := hx i
    change F (g⁻¹ * rootDiagUnit τ (a i) * g) = _ at h
    rw [map_mul, map_mul, map_inv, hFd] at h
    exact h
  have hmC : m ∈ familyCentralizer τ L a := by
    rw [mem_familyCentralizer]
    refine ⟨hmG, fun i => ?_⟩
    have h1 : rootDiagUnit τ (a i) * F g = F g * (g⁻¹ * rootDiagUnit τ (a i) * g) := by
      rw [← hconj i]; group
    change rootDiagUnit τ (a i) * (F g * g⁻¹) * (rootDiagUnit τ (a i))⁻¹ = F g * g⁻¹
    calc _ = (rootDiagUnit τ (a i) * F g) * g⁻¹ * (rootDiagUnit τ (a i))⁻¹ := by group
      _ = F g * g⁻¹ := by rw [h1]; group
  have hmM : m ∈ familyGroup (K := L) a := hcent ▸ hmC
  obtain ⟨z, hz, hzF⟩ := lang_familyGroup ℓ a e he 1 (Subgroup.one_mem _)
    m⁻¹ (inv_mem hmM)
  have hzF' : z⁻¹ * F z = m⁻¹ := by simpa only [one_mul, mul_one, inv_one] using hzF
  have hFz : F z = z * m⁻¹ := by
    calc _ = z * (z⁻¹ * F z) := by group
      _ = z * m⁻¹ := by rw [hzF']
  have hFg : F g = m * g := by dsimp [m]; group
  have hzC : z ∈ familyCentralizer τ L a := familyGroup_le_familyCentralizer a hz
  have hzG : z ∈ adjointGroup τ L := (mem_familyCentralizer.mp hzC).1
  have hzd : ∀ i, z⁻¹ * rootDiagUnit τ (a i) * z = rootDiagUnit τ (a i) := by
    intro i
    have h := (mem_familyCentralizer.mp hzC).2 i
    have hc : rootDiagUnit τ (a i) * z = z * rootDiagUnit τ (a i) := by
      calc _ = (rootDiagUnit τ (a i) * z * (rootDiagUnit τ (a i))⁻¹) * rootDiagUnit τ (a i) := by group
        _ = z * rootDiagUnit τ (a i) := by rw [h]
    calc _ = z⁻¹ * (rootDiagUnit τ (a i) * z) := by group
      _ = rootDiagUnit τ (a i) := by rw [hc]; group
  refine ⟨z * g, mul_mem hzG hg, ?_, fun i => ?_⟩
  · change F (z * g) = z * g
    rw [map_mul, hFz, hFg]
    group
  · calc _ = g⁻¹ * (z⁻¹ * rootDiagUnit τ (a i) * z) * g := by group
      _ = g⁻¹ * rootDiagUnit τ (a i) * g := by rw [hzd]

theorem exists_lang_conj_of_family_twisted {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] {e : ℕ} (he : 1 ≤ e) {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {p : ℕ} (hpq : Nat.Coprime p (ℓ ^ e))
    (hexp : ∀ i j, a i j ^ p = 1) {w : WeylGroup τ}
    (hw : ∀ i v, rootChar (a i) (w • v) = rootChar (a i) v ^ ℓ ^ e)
    (hcent : familyCentralizer τ L a = familyGroup (K := L) a)
    {g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hx : ∀ i, entrywiseFrobGL τ L ℓ e (g * rootDiagUnit τ (a i) * g⁻¹) =
      g * rootDiagUnit τ (a i) * g⁻¹) :
    ∃ g₁ ∈ adjointGroup τ L,
      entrywiseFrobGL τ L ℓ e g₁ = g₁ * canonicalRep (coxeterSystem τ) L w ∧
      ∀ i, g₁ * rootDiagUnit τ (a i) * g₁⁻¹ = g * rootDiagUnit τ (a i) * g⁻¹ := by
  let F := entrywiseFrobGL τ L ℓ e
  let n := canonicalRep (coxeterSystem τ) L w
  have hnG : n ∈ adjointGroup τ L := canonicalRep_mem_adjointGroup _ L _
  have hFd : ∀ i, F (rootDiagUnit τ (a i)) = n⁻¹ * rootDiagUnit τ (a i) * n := by
    intro i
    have h := rootDiagUnit_eq_conj_frob ℓ (hw i)
    change rootDiagUnit τ (a i) = n * F (rootDiagUnit τ (a i)) * n⁻¹ at h
    calc F (rootDiagUnit τ (a i)) = n⁻¹ * (n * F (rootDiagUnit τ (a i)) * n⁻¹) * n := by group
      _ = n⁻¹ * rootDiagUnit τ (a i) * n := by rw [← h]
  have hnN : n ∈ Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)) :=
    canonicalRep_mem_normalizer_of_image (image_familyKernel_of_pow ℓ hpq a hexp hw)
  let m : ModGL τ L := g⁻¹ * F g * n⁻¹
  have hmG : m ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem hg) (entrywiseFrobGL_mem ℓ e hg)) (inv_mem hnG)
  have hmC : m ∈ familyCentralizer τ L a := by
    rw [mem_familyCentralizer]
    refine ⟨hmG, fun i => ?_⟩
    have h := hx i
    change F (g * rootDiagUnit τ (a i) * g⁻¹) = g * rootDiagUnit τ (a i) * g⁻¹ at h
    rw [map_mul, map_mul, map_inv, hFd i] at h
    have h1 : m * rootDiagUnit τ (a i) * m⁻¹ = rootDiagUnit τ (a i) := by
      calc m * rootDiagUnit τ (a i) * m⁻¹ =
          g⁻¹ * (F g * (n⁻¹ * rootDiagUnit τ (a i) * n) * (F g)⁻¹) * g := by
            simp only [m]; group
        _ = rootDiagUnit τ (a i) := by rw [h]; group
    calc rootDiagUnit τ (a i) * m * (rootDiagUnit τ (a i))⁻¹ =
        rootDiagUnit τ (a i) * (m * rootDiagUnit τ (a i) * m⁻¹)⁻¹ * m := by group
      _ = m := by rw [h1]; group
  have hmM : m ∈ familyGroup (K := L) a := hcent ▸ hmC
  obtain ⟨z, hz, hzm⟩ := lang_familyGroup ℓ a e he n hnN m hmM
  change z⁻¹ * (n * F z * n⁻¹) = m at hzm
  have hzC : z ∈ familyCentralizer τ L a := familyGroup_le_familyCentralizer a hz
  obtain ⟨hzG, hzd⟩ := mem_familyCentralizer.1 hzC
  refine ⟨g * z⁻¹, mul_mem hg (inv_mem hzG), ?_, fun i => ?_⟩
  · have hFz : F z = n⁻¹ * (z * m) * n := by
      have h : n * F z * n⁻¹ = z * m := by
        calc n * F z * n⁻¹ = z * (z⁻¹ * (n * F z * n⁻¹)) := by group
          _ = z * m := by rw [hzm]
      calc F z = n⁻¹ * (n * F z * n⁻¹) * n := by group
        _ = n⁻¹ * (z * m) * n := by rw [h]
    have hFg : F g = g * m * n := by simp only [m]; group
    change F (g * z⁻¹) = g * z⁻¹ * n
    rw [map_mul, map_inv, hFz, hFg]
    group
  · have hc := hzd i
    calc g * z⁻¹ * rootDiagUnit τ (a i) * (g * z⁻¹)⁻¹ =
        g * z⁻¹ * rootDiagUnit τ (a i) * z * g⁻¹ := by group
      _ = g * (rootDiagUnit τ (a i) * z * (rootDiagUnit τ (a i))⁻¹)⁻¹ * rootDiagUnit τ (a i) *
          z * g⁻¹ := by rw [hc]
      _ = g * rootDiagUnit τ (a i) * g⁻¹ := by group

theorem exists_lang_conj_of_family_twisted_stab {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] {e : ℕ} (he : 1 ≤ e) {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {p : ℕ} (hpq : Nat.Coprime p (ℓ ^ e))
    (hexp : ∀ i j, a i j ^ p = 1) {w : WeylGroup τ}
    (hw : ∀ i v, rootChar (a i) (w • v) = rootChar (a i) v ^ ℓ ^ e)
    {g : ModGL τ L} (hg : g ∈ adjointGroup τ L)
    (hx : ∀ i, entrywiseFrobGL τ L ℓ e (g * rootDiagUnit τ (a i) * g⁻¹) =
      g * rootDiagUnit τ (a i) * g⁻¹) :
    ∃ v ∈ familyStabilizer a, ∃ g₁ ∈ adjointGroup τ L,
      entrywiseFrobGL τ L ℓ e g₁ = g₁ * (canonicalRep (coxeterSystem τ) L v *
        canonicalRep (coxeterSystem τ) L w) ∧
      ∀ i, g₁ * rootDiagUnit τ (a i) * g₁⁻¹ = g * rootDiagUnit τ (a i) * g⁻¹ := by
  let F := entrywiseFrobGL τ L ℓ e
  let n := canonicalRep (coxeterSystem τ) L w
  have hnG : n ∈ adjointGroup τ L := canonicalRep_mem_adjointGroup _ L _
  have hFd : ∀ i, F (rootDiagUnit τ (a i)) = n⁻¹ * rootDiagUnit τ (a i) * n := by
    intro i
    have h := rootDiagUnit_eq_conj_frob ℓ (hw i)
    change rootDiagUnit τ (a i) = n * F (rootDiagUnit τ (a i)) * n⁻¹ at h
    calc F (rootDiagUnit τ (a i)) = n⁻¹ * (n * F (rootDiagUnit τ (a i)) * n⁻¹) * n := by group
      _ = n⁻¹ * rootDiagUnit τ (a i) * n := by rw [← h]
  have hnN : n ∈ Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)) :=
    canonicalRep_mem_normalizer_of_image (image_familyKernel_of_pow ℓ hpq a hexp hw)
  let m : ModGL τ L := g⁻¹ * F g * n⁻¹
  have hmG : m ∈ adjointGroup τ L :=
    mul_mem (mul_mem (inv_mem hg) (entrywiseFrobGL_mem ℓ e hg)) (inv_mem hnG)
  have hmC : m ∈ familyCentralizer τ L a := by
    rw [mem_familyCentralizer]
    refine ⟨hmG, fun i => ?_⟩
    have h := hx i
    change F (g * rootDiagUnit τ (a i) * g⁻¹) = g * rootDiagUnit τ (a i) * g⁻¹ at h
    rw [map_mul, map_mul, map_inv, hFd i] at h
    have h1 : m * rootDiagUnit τ (a i) * m⁻¹ = rootDiagUnit τ (a i) := by
      calc m * rootDiagUnit τ (a i) * m⁻¹ =
          g⁻¹ * (F g * (n⁻¹ * rootDiagUnit τ (a i) * n) * (F g)⁻¹) * g := by
            simp only [m]; group
        _ = rootDiagUnit τ (a i) := by rw [h]; group
    calc rootDiagUnit τ (a i) * m * (rootDiagUnit τ (a i))⁻¹ =
        rootDiagUnit τ (a i) * (m * rootDiagUnit τ (a i) * m⁻¹)⁻¹ * m := by group
      _ = m := by rw [h1]; group
  obtain ⟨v, hv, μ, hμ, hmv⟩ := familyCentralizer_le_mul τ L a hmC
  let Q := canonicalRep (coxeterSystem τ) L v * n
  have hQN : Q ∈ Subgroup.normalizer (familyGroup (K := L) a : Set (ModGL τ L)) :=
    mul_mem (canonicalRep_mem_normalizer_familyGroup hv) hnN
  have hFg : F g = g * μ * Q := by
    have h : g⁻¹ * F g * n⁻¹ = μ * canonicalRep (coxeterSystem τ) L v := hmv
    calc F g = g * (g⁻¹ * F g * n⁻¹) * n := by group
      _ = g * μ * Q := by rw [h]; simp only [Q]; group
  obtain ⟨z, hz, hzm⟩ := lang_familyGroup ℓ a e he Q hQN μ hμ
  change z⁻¹ * (Q * F z * Q⁻¹) = μ at hzm
  have hzC : z ∈ familyCentralizer τ L a := familyGroup_le_familyCentralizer a hz
  obtain ⟨hzG, hzd⟩ := mem_familyCentralizer.1 hzC
  refine ⟨v, hv, g * z⁻¹, mul_mem hg (inv_mem hzG), ?_, fun i => ?_⟩
  · have hFz : F z = Q⁻¹ * (z * μ) * Q := by
      have h : Q * F z * Q⁻¹ = z * μ := by
        calc Q * F z * Q⁻¹ = z * (z⁻¹ * (Q * F z * Q⁻¹)) := by group
          _ = z * μ := by rw [hzm]
      calc F z = Q⁻¹ * (Q * F z * Q⁻¹) * Q := by group
        _ = Q⁻¹ * (z * μ) * Q := by rw [h]
    change F (g * z⁻¹) = g * z⁻¹ * Q
    rw [map_mul, map_inv, hFz, hFg]
    group
  · have hc := hzd i
    calc g * z⁻¹ * rootDiagUnit τ (a i) * (g * z⁻¹)⁻¹ =
        g * z⁻¹ * rootDiagUnit τ (a i) * z * g⁻¹ := by group
      _ = g * (rootDiagUnit τ (a i) * z * (rootDiagUnit τ (a i))⁻¹)⁻¹ * rootDiagUnit τ (a i) *
          z * g⁻¹ := by rw [hc]
      _ = g * rootDiagUnit τ (a i) * g⁻¹ := by group

theorem exists_frobenius_fixed_conj_of_toral {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ] {e : ℕ} (he : 1 ≤ e) {a : Fin τ.rank → Lˣ}
    (ha : ∀ i, a i ^ ℓ ^ e = a i)
    (hstab : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) {g : ModGL τ L}
    (hg : g ∈ adjointGroup τ L)
    (hx : entrywiseFrobGL τ L ℓ e (g⁻¹ * rootDiagUnit τ a * g) = g⁻¹ * rootDiagUnit τ a * g) :
    ∃ h ∈ adjointGroup τ L, entrywiseFrobGL τ L ℓ e h = h ∧
      h⁻¹ * rootDiagUnit τ a * h = g⁻¹ * rootDiagUnit τ a * g  := by
  let afam : Unit → Fin τ.rank → Lˣ := fun _ => a
  have hkernel : familyKernel afam = rootCharKernel a := by
    ext α
    simp only [familyKernel, rootCharKernel, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hα, h⟩; exact ⟨hα, h ()⟩
    · rintro ⟨hα, h⟩; exact ⟨hα, fun _ => h⟩
  have hgroup : familyGroup (K := L) afam = toralRootGroup τ L a := by
    simp only [familyGroup, toralRootGroup, hkernel]
  have hcentral : familyCentralizer τ L afam = toralCentralizer τ L a := by
    ext x
    rw [mem_familyCentralizer, mem_toralCentralizer]
    simp only [afam, forall_const]
  have hcent : familyCentralizer τ L afam = familyGroup (K := L) afam := by
    rw [hcentral, hgroup, toralCentralizer_eq_toralRootGroup_of_stabilizer_le τ L a hstab]
  obtain ⟨h, hh, hFh, hconj⟩ := exists_frobenius_fixed_conj_of_family ℓ he afam
    (fun _ j => ha j) hcent hg (fun _ => hx)
  exact ⟨h, hh, hFh, hconj ()⟩

end CFSG.StandardType.ExcElemToral
