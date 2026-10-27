module

public import CFSG.Quasithin.Background.C116Two.NatMod
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_of_acts_trivially {L : Subgroup G} {l : G} (hl : l ∈ L)
    (htriv : ∀ u ∈ blockU L, ⁅u, l⁆ ∈ blockZ L) {u : G} (hu : u ∈ blockU L) :
    l * u * l⁻¹ ∈ blockU L ∧ (l * u * l⁻¹) * u⁻¹ ∈ blockZ L := by
  have h1 : l * u * l⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp
    (C1.le_normalizer_blockU L hl) u).mp hu
  refine ⟨h1, ?_⟩
  have h2 := htriv u hu
  have : (l * u * l⁻¹) * u⁻¹ = (⁅u, l⁆)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [this]
  exact (blockZ L).inv_mem h2

theorem acts_trivially_mem_blockQ {L : Subgroup G} {V : Type} [CommGroup V] (D : ModData L V)
    {l : G} (hl : l ∈ L) (htriv : ∀ u ∈ blockU L, ⁅u, l⁆ ∈ blockZ L) : l ∈ blockQ L := by
  apply D.faithful ⟨l, hl⟩
  ext x
  obtain ⟨u, rfl⟩ := D.surj x
  obtain ⟨hv, hz⟩ := conj_mem_of_acts_trivially hl htriv u.2
  have hzU : (l * (u : G) * l⁻¹) * (u : G)⁻¹ ∈ blockU L :=
    (blockU L).mul_mem hv ((blockU L).inv_mem u.2)
  have hzker : (⟨(l * (u : G) * l⁻¹) * (u : G)⁻¹, hzU⟩ : ↥(blockU L)) ∈ D.β.ker := by
    rw [D.ker]
    exact Subgroup.mem_subgroupOf.mpr hz
  have hvu : (⟨l * (u : G) * l⁻¹, hv⟩ : ↥(blockU L)) =
      ⟨(l * (u : G) * l⁻¹) * (u : G)⁻¹, hzU⟩ * u := by
    apply Subtype.ext
    simp
  have hβv : D.β ⟨l * (u : G) * l⁻¹, hv⟩ = D.β u := by
    rw [hvu, map_mul, (MonoidHom.mem_ker.mp hzker), one_mul]
  have := D.equiv ⟨l, hl⟩ u ⟨l * (u : G) * l⁻¹, hv⟩ rfl
  rw [hβv] at this
  simpa using this.symm

theorem kernel_lemma {L : Subgroup G} {V : Type} [CommGroup V] (D : ModData L V) (hL : IsShort2 L)
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (htriv : ∀ u ∈ blockU L, ⁅u, a⁆ ∈ blockZ L) : ∀ u ∈ blockU L, ⁅u, a⁆ = 1 := by
  have hcomm : ∀ x ∈ blockU L, ∀ y ∈ blockU L, x * y = y * x := (C1.elemAb2_blockU hL).1
  have haU : ∀ u ∈ blockU L, a * u * a⁻¹ ∈ blockU L := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU ha) u).mp hu
  have haiU : ∀ u ∈ blockU L, a⁻¹ * u * a ∈ blockU L := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU ha) (a⁻¹ * u * a)).mpr
      (by simpa [mul_assoc] using hu)
    exact this
  have haZ : ∀ z ∈ blockZ L, a * z * a⁻¹ ∈ blockZ L := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockZ ha) z).mp hz
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hZc : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z = z * l := fun z hz l hl =>
    (Subgroup.mem_centralizer_iff.mp hz.2 l hl)
  have h1 : ∀ u ∈ blockU L, (a * u * a⁻¹) * u⁻¹ ∈ blockZ L := fun u hu => by
    have := (blockZ L).inv_mem (htriv u hu)
    have e : (a * u * a⁻¹) * u⁻¹ = (⁅u, a⁆)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]; exact this
  have h2 : ∀ u ∈ blockU L, (a⁻¹ * u * a) * u⁻¹ ∈ blockZ L := fun u hu => by
    have := htriv (a⁻¹ * u * a) (haiU u hu)
    have e : (a⁻¹ * u * a) * u⁻¹ = ⁅a⁻¹ * u * a, a⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]; exact this
  have hsame : ∀ l ∈ L, ∀ u ∈ blockU L, (a * l * a⁻¹) * u * (a * l * a⁻¹)⁻¹ = l * u * l⁻¹ := by
    intro l hl u hu
    have hl' : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ha l).mp hl
    set c := (a * l * a⁻¹) * l⁻¹ with hc
    have hcL : c ∈ L := L.mul_mem hl' (L.inv_mem hl)
    have hcQ : c ∈ blockQ L := by
      refine acts_trivially_mem_blockQ D hcL fun v hv => ?_
      set v₁ := l⁻¹ * v * l with hv₁
      have hv₁U : v₁ ∈ blockU L := by
        have := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L (L.inv_mem hl)) v).mp hv
        simpa [hv₁, mul_assoc] using this
      set v₂ := a⁻¹ * v₁ * a with hv₂
      have hv₂U : v₂ ∈ blockU L := haiU v₁ hv₁U
      set z₂ := v₂ * v₁⁻¹ with hz₂
      have hz₂Z : z₂ ∈ blockZ L := h2 v₁ hv₁U
      set z₄ := (a * v * a⁻¹) * v⁻¹ with hz₄
      have hz₄Z : z₄ ∈ blockZ L := h1 v hv
      set z₃ := a * z₂ * a⁻¹ with hz₃
      have hz₃Z : z₃ ∈ blockZ L := haZ z₂ hz₂Z
      have e1 : c * v * c⁻¹ = (a * l * a⁻¹) * v₁ * (a * l * a⁻¹)⁻¹ := by
        rw [hc, hv₁]; group
      have e2 : (a * l * a⁻¹) * v₁ * (a * l * a⁻¹)⁻¹ = a * (l * v₂ * l⁻¹) * a⁻¹ := by
        rw [hv₂]; group
      have e3 : l * v₂ * l⁻¹ = z₂ * v := by
        have : v₂ = z₂ * v₁ := by rw [hz₂]; group
        rw [this]
        have hz : l * z₂ * l⁻¹ = z₂ := by
          have := hZc z₂ hz₂Z l hl
          rw [this]; group
        calc l * (z₂ * v₁) * l⁻¹ = (l * z₂ * l⁻¹) * (l * v₁ * l⁻¹) := by group
          _ = z₂ * v := by rw [hz, hv₁]; group
      have e4 : c * v * c⁻¹ = (z₃ * z₄) * v := by
        rw [e1, e2, e3]
        rw [hz₃, hz₄]; group
      have hz34 : z₃ * z₄ ∈ blockZ L := (blockZ L).mul_mem hz₃Z hz₄Z
      have e5 : ⁅v, c⁆ = (z₃ * z₄)⁻¹ := by
        have : ⁅v, c⁆ = v * (c * v * c⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [this, e4]
        have hzv : (z₃ * z₄) * v = v * (z₃ * z₄) := (hcomm _ (hZU hz34) v hv)
        rw [mul_inv_rev]
        group
      rw [e5]
      exact (blockZ L).inv_mem hz34
    have hxU : l * u * l⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp
      (C1.le_normalizer_blockU L hl) u).mp hu
    have hcx : (l * u * l⁻¹) * c = c * (l * u * l⁻¹) := C1.blockU_comm hL _ hxU c hcQ
    calc (a * l * a⁻¹) * u * (a * l * a⁻¹)⁻¹ = c * (l * u * l⁻¹) * c⁻¹ := by rw [hc]; group
      _ = (l * u * l⁻¹) * c * c⁻¹ := by rw [← hcx]
      _ = l * u * l⁻¹ := by group
  have h4 : ∀ u ∈ blockU L, ∀ l ∈ L, a * ⁅u, l⁆ * a⁻¹ = ⁅u, l⁆ := by
    intro u hu l hl
    have hu' : a * u * a⁻¹ ∈ blockU L := haU u hu
    set z := (a * u * a⁻¹) * u⁻¹ with hz
    have hzZ : z ∈ blockZ L := h1 u hu
    have e1 : a * (l * u * l⁻¹) * a⁻¹ = l * (a * u * a⁻¹) * l⁻¹ := by
      have := hsame l hl (a * u * a⁻¹) hu'
      have e : (a * l * a⁻¹) * (a * u * a⁻¹) * (a * l * a⁻¹)⁻¹ = a * (l * u * l⁻¹) * a⁻¹ := by group
      rw [e] at this; exact this
    have e2 : a * u * a⁻¹ = z * u := by rw [hz]; group
    have hzl : l * z * l⁻¹ = z := by
      have := hZc z hzZ l hl
      rw [this]; group
    have e3 : l * (a * u * a⁻¹) * l⁻¹ = z * (l * u * l⁻¹) := by
      rw [e2]
      calc l * (z * u) * l⁻¹ = (l * z * l⁻¹) * (l * u * l⁻¹) := by group
        _ = z * (l * u * l⁻¹) := by rw [hzl]
    have hxU : l * u * l⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp
      (C1.le_normalizer_blockU L hl) u).mp hu
    have hcz : (z : G) * u = u * z := hcomm z (hZU hzZ) u hu
    have hcz' : z * (l * u * l⁻¹)⁻¹ = (l * u * l⁻¹)⁻¹ * z := hcomm z (hZU hzZ) _ ((blockU L).inv_mem hxU)
    calc a * ⁅u, l⁆ * a⁻¹ = (a * u * a⁻¹) * (a * (l * u * l⁻¹) * a⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (z * u) * (z * (l * u * l⁻¹))⁻¹ := by rw [← e2, e1, e3]
      _ = ⁅u, l⁆ := by
        simp only [commutatorElement_def]
        have : (z * (l * u * l⁻¹))⁻¹ = (l * u * l⁻¹)⁻¹ * z⁻¹ := by group
        rw [this]
        have hzu : z⁻¹ * u = u * z⁻¹ := by
          have := hcomm (z⁻¹) ((blockU L).inv_mem (hZU hzZ)) u hu
          exact this
        calc z * u * ((l * u * l⁻¹)⁻¹ * z⁻¹) = z * (u * (l * u * l⁻¹)⁻¹) * z⁻¹ := by group
          _ = u * (l * u * l⁻¹)⁻¹ := by
            have hy : u * (l * u * l⁻¹)⁻¹ ∈ blockU L :=
              (blockU L).mul_mem hu ((blockU L).inv_mem hxU)
            have := hcomm z (hZU hzZ) _ hy
            rw [this]; group
          _ = u * l * u⁻¹ * l⁻¹ := by group
  intro u hu
  have hle : blockU L ≤ blockU L ⊓ Subgroup.centralizer ({a} : Set G) := by
    conv_lhs => rw [← C1.commutator_blockU hL]
    rw [Subgroup.commutator_le]
    intro x hx l hl
    refine ⟨C1.commutator_blockU_le L (Subgroup.commutator_mem_commutator hx hl),
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := h4 x hx l hl
    calc h * ⁅x, l⁆ = (h * ⁅x, l⁆ * h⁻¹) * h := by group
      _ = ⁅x, l⁆ * h := by rw [this]
  have hua := Subgroup.mem_centralizer_iff.mp (hle hu).2 a rfl
  simp only [commutatorElement_def]
  calc u * a * u⁻¹ * a⁻¹ = (u * a) * u⁻¹ * a⁻¹ := by group
    _ = (a * u) * u⁻¹ * a⁻¹ := by rw [← hua]
    _ = 1 := by group

end CFSG.Quasithin.C116Two
