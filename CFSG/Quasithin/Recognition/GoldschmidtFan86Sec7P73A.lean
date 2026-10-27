module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73Fin1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XD10
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P73Idx

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace P73

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem exists_d10Set_at (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) {α : V}
    (hα : valence Γ α = 5) : Nonempty (D10Set L α) := by
  obtain ⟨Q₁, Q₂, h10, h20, h1ne⟩ := exists_two_arcs F α
  obtain ⟨D, -⟩ := P4X.exists_d10Set_arcs h71a h71c hα Q₁ Q₂ h10 h20 h1ne
  exact ⟨D⟩

theorem fan73a_of (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) (h40 : Fan40 F)
    (h64 : Fan64 F) (h65 : Fan65 F) : Fan73a F := by
  intro α hα
  obtain ⟨D⟩ := exists_d10Set_at F h71a h71c hα
  obtain ⟨hidx, hW⟩ := relIndex_AB D F h71a h71c h40 h64 h65
  exact ⟨hidx, fun g hg => sq_mem D F h71c hg, fun g hg h hh => comm_mem D F h71c hg hh,
    fun N hBN hNA hinv => minimal_of D hW F h71c hBN hNA hinv, noncentral_of D hW F h71c⟩

end P73

end CFSG.Quasithin.Fan86
